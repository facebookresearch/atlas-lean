/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.GGM
public import Mathlib.Data.ZMod.Defs

/-!
# Tests for the GGM construction

* The construction follows the bits of the input from the key, first bit first, and on the empty
  input it is the key.
* The lazy table answers a repeated query from the table, without reading the tape, and stops
  with its default output at a fresh query past the end of the tape.
* An adversary that makes no queries has PRF advantage `0`, whatever the keyed function: the case
  `Q = 0` that `prfAdvantage_ggm` leaves out.
* The equality of `prfAdvantage_ggm` on an example, with both sides computed by counting. With the
  generator `G s = (s, s)` and `ℓ = 1`, the GGM function is `F k x = k`. The adversary that
  compares the answers at `0` and `1` has PRF advantage `1/2` and makes `Q = 2` queries. The
  hybrid distinguisher has PRG advantage `1/4`: with hybrid index `0` its challenge labels both
  children of the root, which the adversary compares, and with hybrid index `1` the challenge is
  never used.
-/

@[expose] public section

namespace Cslib.Crypto.GGMTests

open Cslib.Crypto.Framework Cslib.Crypto.GGM
open Cslib.Crypto.Framework.OracleComp (runLazy)
open Cslib.Crypto.Framework.LazySampling (Table)

/-- An affine generator on `ZMod 7`. -/
def affineG (s : ZMod 7) : ZMod 7 × ZMod 7 := (s + 1, 2 * s)

/-- The first bit is used first: `F(3, 10) = G₀(G₁(3)) = 2 * 3 + 1`. -/
example : ggm affineG 3 ![true, false] = 0 := by decide

example : ggm affineG 3 ![false, true] = 1 := by decide

/-- On the empty input the construction is the key. -/
example (k : ZMod 7) : ggm affineG k (Fin.elim0 : Fin 0 → Bool) = k := rfl

/-- Query `false` twice and output whether the two answers agree. -/
def askTwice : OracleComp Bool Bool Bool :=
  .liftBind false fun a => .liftBind false fun b => .pure (a == b)

/-- The repeated query is answered from the table, so the second tape entry is never read. -/
example : runLazy ![true, false] false 0 Table.empty askTwice = true := by decide

/-- Query `false`, then `true`, and output whether the answers agree. -/
def askBoth : OracleComp Bool Bool Bool :=
  .liftBind false fun a => .liftBind true fun b => .pure (a == b)

/-- A tape of two answers serves two fresh queries. -/
example : runLazy ![true, false] false 0 Table.empty askBoth = false := by decide

/-- With a tape of one answer, the second fresh query stops the run with the default output. -/
example : runLazy ![true] true 0 Table.empty askBoth = true := by decide

/-- An adversary that makes no queries has PRF advantage `0`. -/
theorem prfAdvantage_eq_zero_of_isQueryBounded_zero {K X Y R : Type*} [Fintype K] [Nonempty K]
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype R] [Nonempty R]
    (F : K → X → Y) (A : R → OracleComp X Y Bool) (hA : ∀ r, FreeM.IsQueryBounded 0 (A r)) :
    PRF.prfAdvantage F A = 0 := by
  let c : R → Bool := fun r => (A r).run fun _ => Classical.arbitrary Y
  have hrun : ∀ r O, (A r).run O = c r := by
    intro r O
    obtain ⟨x, hx, -⟩ := FreeM.eq_pure_of_isQueryBoundedWith_zero (hA r)
    simp only [c, hx]
    rfl
  have hreal : PRF.prfReal F A = (Cslib.Probability.PMF.uniformOfFintype R).map c := by
    rw [PRF.prfReal, ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, hrun]
    exact PMF.bind_const _ _
  have hrand : PRF.prfRand A = (Cslib.Probability.PMF.uniformOfFintype R).map c := by
    rw [PRF.prfRand, ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, hrun]
    exact PMF.bind_const _ _
  rw [PRF.prfAdvantage, hreal, hrand, sub_self, abs_zero]

/-- The generator that copies its seed. -/
def copyG (s : Bool) : Bool × Bool := (s, s)

/-- With `copyG`, the GGM function ignores its input. -/
example (k : Bool) (x : Fin 1 → Bool) : ggm copyG k x = k := by
  revert k x
  decide

/-- Compare the answers at the two inputs of length `1`. -/
def compare : Unit → OracleComp (Fin 1 → Bool) Bool Bool :=
  fun _ => .liftBind ![false] fun a => .liftBind ![true] fun b => .pure (a == b)

theorem compare_queryBounded (r : Unit) : FreeM.IsQueryBounded 2 (compare r) :=
  fun _ _ => trivial

/-- A function on the two inputs of length `1` is the pair of its values. -/
def funEquiv : ((Fin 1 → Bool) → Bool) × Unit ≃ (Bool × Bool) × Unit :=
  ((Equiv.arrowCongr (Equiv.funUnique (Fin 1) Bool) (Equiv.refl Bool)).trans
    (Equiv.boolArrowEquivProd Bool)).prodCongr (Equiv.refl Unit)

theorem prfAdvantage_compare : PRF.prfAdvantage (ggm copyG) compare = 1 / 2 := by
  change advantage (PRF.prfReal (ggm copyG) compare) (PRF.prfRand compare) = 1 / 2
  rw [advantage, PRF.prfReal, PRF.prfRand,
    ← Cslib.Probability.PMF.uniformOfFintype_map_equiv funEquiv.symm, PMF.map_comp,
    winProb_map_uniform, winProb_map_uniform]
  have h1 : (Finset.univ.filter fun ω : Bool × Unit =>
      (compare ω.2).run (ggm copyG ω.1) = true).card = 2 := by decide
  have h2 : (Finset.univ.filter fun ω : (Bool × Bool) × Unit =>
      ((fun ω : ((Fin 1 → Bool) → Bool) × Unit => (compare ω.2).run ω.1) ∘ funEquiv.symm) ω =
        true).card = 2 := by decide
  rw [h1, h2]
  norm_num

/-- The coins of the hybrid distinguisher for `ℓ = 1`, `Q = 2` and seeds in `Bool`, with the tapes
written as pairs. -/
def coinsEquiv : (Fin 1 × Fin 2 × (Fin 2 → Bool × Bool) × (Fin 2 → Bool) × Unit) ≃
    (Fin 1 × Fin 2 × ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool) × Unit) :=
  (Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr
    ((finTwoArrowEquiv _).prodCongr ((finTwoArrowEquiv _).prodCongr (Equiv.refl _))))

/-- The hybrid distinguisher built from `compare` has PRG advantage `1/4`, by counting: it outputs
`1` with probability `3/4` on `copyG` of a uniform seed and `1/2` on a uniform pair. -/
theorem prgAdvantage_ggmReduction_compare :
    PRG.prgAdvantage copyG (ggmReduction copyG 2 compare) = 1 / 4 := by
  have hcoins : (ggmReduction copyG 2 compare).coins =
      (Cslib.Probability.PMF.uniformOfFintype _).map coinsEquiv.symm :=
    (Cslib.Probability.PMF.uniformOfFintype_map_equiv coinsEquiv.symm).symm
  have hreal := uniformOfFintype_map_prod (α := Bool) fun p : Bool × _ =>
    (ggmReduction copyG 2 compare).guess (copyG p.1) (coinsEquiv.symm p.2)
  have hrand := uniformOfFintype_map_prod (α := Bool × Bool) fun p : (Bool × Bool) × _ =>
    (ggmReduction copyG 2 compare).guess p.1 (coinsEquiv.symm p.2)
  dsimp only at hreal hrand
  rw [PRG.prgAdvantage, advantage, PRG.prgReal, PRG.prgRand, hcoins]
  simp only [PMF.map_comp, Function.comp_def]
  rw [← hreal, ← hrand, winProb_map_uniform, winProb_map_uniform]
  have h1 : (Finset.univ.filter fun p : Bool × (Fin 1 × Fin 2 × ((Bool × Bool) × (Bool × Bool)) ×
      (Bool × Bool) × Unit) =>
      (ggmReduction copyG 2 compare).guess (copyG p.1) (coinsEquiv.symm p.2) = true).card =
      192 := by decide +kernel
  have h2 : (Finset.univ.filter fun p : (Bool × Bool) × (Fin 1 × Fin 2 ×
      ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool) × Unit) =>
      (ggmReduction copyG 2 compare).guess p.1 (coinsEquiv.symm p.2) = true).card =
      256 := by decide +kernel
  rw [h1, h2]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Fintype.card_unit]
  norm_num

/-- So the two sides of `prfAdvantage_ggm` agree on the example: `1/2 = 1 * 2 * (1/4)`. -/
example : PRF.prfAdvantage (ggm copyG) compare =
    (1 : ℕ) * (2 : ℕ) * PRG.prgAdvantage copyG (ggmReduction copyG 2 compare) := by
  rw [prfAdvantage_compare, prgAdvantage_ggmReduction_compare]
  norm_num

/-- The same equality, from `prfAdvantage_ggm`. -/
example : PRF.prfAdvantage (ggm copyG) compare =
    (1 : ℕ) * (2 : ℕ) * PRG.prgAdvantage copyG (ggmReduction copyG 2 compare) :=
  prfAdvantage_ggm copyG 2 compare compare_queryBounded

end Cslib.Crypto.GGMTests
