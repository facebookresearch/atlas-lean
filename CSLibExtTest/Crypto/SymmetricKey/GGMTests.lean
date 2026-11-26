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
* The lazy simulation answers a repeated query from its table, without reading the tape, and
  stops with its default output at a fresh query past the end of the tape.
* The equality of `prfAdvantage_ggm` on an example. With the generator `G s = (s, s)` and
  `ℓ = 1`, the GGM function is `F k x = k`. The adversary that compares the answers at `0` and `1`
  has PRF advantage `1/2` and makes `Q = 2` queries, so the hybrid distinguisher has PRG advantage
  `1/4`: with hybrid index `0` its challenge labels both children of the root, which the
  adversary compares, and with hybrid index `1` the challenge is never used.
-/

@[expose] public section

namespace Cslib.Crypto.GGMTests

open Cslib.Crypto.Framework Cslib.Crypto.GGM

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
example : simLazy ![true, false] false 0 LazySampling.Table.empty askTwice = true := by decide

/-- Query `false`, then `true`, and output whether the answers agree. -/
def askBoth : OracleComp Bool Bool Bool :=
  .liftBind false fun a => .liftBind true fun b => .pure (a == b)

/-- A tape of two answers serves two fresh queries. -/
example : simLazy ![true, false] false 0 LazySampling.Table.empty askBoth = false := by decide

/-- With a tape of one answer, the second fresh query stops the run with the default output. -/
example : simLazy ![true] true 0 LazySampling.Table.empty askBoth = true := by decide

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

/-- `prfAdvantage_ggm` with `ℓ = 1` and `Q = 2`: the hybrid distinguisher has advantage `1/4`. -/
example : PRG.prgAdvantage copyG (ggmReduction copyG 2 compare) = 1 / 4 := by
  have h := prfAdvantage_ggm copyG 2 compare compare_queryBounded
  rw [prfAdvantage_compare] at h
  norm_num at h
  linarith

end Cslib.Crypto.GGMTests
