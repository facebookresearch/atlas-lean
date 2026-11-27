/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.PRGFromPRF
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for pseudorandom generators from pseudorandom functions

* On a small instance the generator evaluates the keyed function at the points, and the reduction
  asks exactly the points as queries and outputs the distinguisher's guess on the answers. With no
  points (`n = 0`) it asks nothing.
* **Without expansion.** The identity keyed function `F k = k` on `Fin n → ZMod 2` is a perfect
  PRF: its two worlds coincide. With the points `x = id` its generator is the identity, which has
  as many keys as outputs, and `prgAdvantage_prgOfPRF_eq` still applies and gives PRG advantage
  `0`: the equality needs no expansion.
* **Distinctness is needed.** With the repeated point `x = (), ()` and `F k () = k`, the generator
  is the doubling map `k ↦ (k, k)` on `ZMod 2`. The equality test has PRG advantage `1/2` against
  it, while its reduction asks the same query twice, gets equal answers in both worlds and has PRF
  advantage `0`. So the conclusion of `prgAdvantage_prgOfPRF_eq` fails for points that are not
  distinct.
* **The asymptotic theorem applies.** For the constant keyed function on one key, one point and
  outputs in `ZMod 2`, every PRF distinguisher family whose output does not depend on the oracle
  has advantage `0`, and the reductions of the distinguishers that ignore their input are such
  families, so `prgSecure_prgOfPRF` makes the one-key generator `PRGSecure` against the
  distinguishers that ignore their input.
-/

@[expose] public section

namespace Cslib.Crypto.PRGFromPRFTests

open Cslib.Crypto.Framework Cslib.Crypto.PRG

/-! ### A small instance -/

/-- A keyed function on `ZMod 5`. -/
def addKey (k x : ZMod 5) : ZMod 5 := k + x

/-- Two distinct points of `ZMod 5`. -/
def pts : Fin 2 → ZMod 5 := ![1, 3]

example : prgOfPRF addKey pts 2 = ![3, 0] := by decide

/-- A distinguisher that checks whether the two halves of its input differ by `2`. -/
noncomputable def diffTwo : Distinguisher (Fin 2 → ZMod 5) Unit :=
  ⟨Cslib.Probability.PMF.uniformOfFintype Unit, fun y _ => decide (y 1 = y 0 + 2)⟩

example (O : ZMod 5 → ZMod 5) : (prgOfPRFReduction pts diffTwo ()).queries O = [1, 3] :=
  queries_prgOfPRFReduction pts diffTwo () O

example : (prgOfPRFReduction pts diffTwo ()).run (addKey 4) = true := by
  rw [run_prgOfPRFReduction]
  decide

example : (prgOfPRFReduction pts diffTwo ()).run (· * 2) = false := by
  rw [run_prgOfPRFReduction]
  decide

/-- A distinguisher for the empty string. -/
noncomputable def emptyD : Distinguisher (Fin 0 → ZMod 5) Unit :=
  ⟨Cslib.Probability.PMF.uniformOfFintype Unit, fun _ _ => true⟩

/-- With no points the reduction asks no query. -/
example (x : Fin 0 → ZMod 5) (O : ZMod 5 → ZMod 5) :
    (prgOfPRFReduction x emptyD ()).queries O = [] := by
  rw [queries_prgOfPRFReduction]
  rfl

/-! ### The equality needs no expansion -/

/-- The identity keyed function on bit strings. -/
def idKey (n : ℕ) (k : Fin n → ZMod 2) : Fin n → ZMod 2 := k

/-- The identity keyed function is a perfect PRF: its two worlds coincide. -/
theorem prfAdvantage_idKey {n : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (D : S → OracleComp (Fin n) (ZMod 2) Bool) : PRF.prfAdvantage (idKey n) D = 0 := by
  simp [PRF.prfAdvantage, PRF.prfReal, PRF.prfRand, idKey]

/-- The generator of the identity keyed function at all points has as many keys as outputs, and
its PRG advantage is `0` against every distinguisher with uniform coins. -/
example {n : ℕ} {R : Type*} [Fintype R] [Nonempty R] (A : Distinguisher (Fin n → ZMod 2) R)
    (hA : A.coins = Cslib.Probability.PMF.uniformOfFintype R) :
    Fintype.card (Fin n → ZMod 2) = Fintype.card (ZMod 2) ^ n ∧
      prgAdvantage (prgOfPRF (idKey n) id) A = 0 := by
  refine ⟨by simp, ?_⟩
  rw [(prgAdvantage_prgOfPRF_eq (idKey n) Function.injective_id A hA).2.2, prfAdvantage_idKey]

/-! ### Distinctness is needed -/

/-- The keyed function `F k () = k`. -/
def keyOut (k : ZMod 2) (_ : Unit) : ZMod 2 := k

/-- The repeated point `(), ()`. -/
def twoUnits : Fin 2 → Unit := fun _ => ()

/-- The equality test on pairs, with uniform coins on `Unit`. -/
noncomputable def eqTest : Distinguisher (Fin 2 → ZMod 2) Unit :=
  ⟨Cslib.Probability.PMF.uniformOfFintype Unit, fun y _ => decide (y 0 = y 1)⟩

theorem not_injective_twoUnits : ¬ Function.Injective twoUnits :=
  fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)

/-- The equality test has PRG advantage `1/2` against the doubling map `k ↦ (k, k)`. -/
theorem prgAdvantage_keyOut_eqTest : prgAdvantage (prgOfPRF keyOut twoUnits) eqTest = 1 / 2 := by
  have hreal : prgReal (prgOfPRF keyOut twoUnits) eqTest = PMF.pure true := by
    simp [prgReal, eqTest, prgOfPRF, keyOut, Cslib.Probability.PMF.uniformOfFintype_unique,
      PMF.pure_map]
  have hrand : prgRand eqTest = (Cslib.Probability.PMF.uniformOfFintype (Fin 2 → ZMod 2)).map
      fun y => decide (y 0 = y 1) := by
    simp only [prgRand, eqTest, Cslib.Probability.PMF.uniformOfFintype_unique, PMF.pure_map]
    rfl
  have hc : (Finset.univ.filter fun y : Fin 2 → ZMod 2 => decide (y 0 = y 1) = true).card = 2 := by
    decide
  rw [prgAdvantage, advantage, hreal, hrand, winProb_map_uniform, hc, winProb_pure]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

/-- The reduction asks `()` twice and gets equal answers, so its PRF advantage is `0`. -/
theorem prfAdvantage_keyOut_eqTest :
    PRF.prfAdvantage keyOut (prgOfPRFReduction twoUnits eqTest) = 0 := by
  have h : ∀ (O : Unit → ZMod 2) (r : Unit),
      (prgOfPRFReduction twoUnits eqTest r).run O = true := by
    intro O r
    rw [run_prgOfPRFReduction]
    simp [eqTest, twoUnits]
  simp [PRF.prfAdvantage, PRF.prfReal, PRF.prfRand, h]

/-- For the repeated point the advantages differ, so `prgAdvantage_prgOfPRF_eq` needs distinct
points. -/
example : prgAdvantage (prgOfPRF keyOut twoUnits) eqTest ≠
    PRF.prfAdvantage keyOut (prgOfPRFReduction twoUnits eqTest) := by
  rw [prgAdvantage_keyOut_eqTest, prfAdvantage_keyOut_eqTest]
  norm_num

/-! ### The asymptotic theorem applies -/

/-- A test of the second component of a uniform pair is a test of a uniform second component. -/
theorem map_snd_uniformOfFintype {Ω S : Type*} [Fintype Ω] [Nonempty Ω] [Fintype S]
    [Nonempty S] (g : S → Bool) :
    (Cslib.Probability.PMF.uniformOfFintype (Ω × S)).map (fun ω => g ω.2) =
      (Cslib.Probability.PMF.uniformOfFintype S).map g := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map_comp]
  exact PMF.bind_const (Cslib.Probability.PMF.uniformOfFintype Ω)
    ((Cslib.Probability.PMF.uniformOfFintype S).map g)

/-- A PRF distinguisher whose output does not depend on the oracle has PRF advantage `0`. -/
theorem prfAdvantage_of_blind {K X Y S : Type*} [Fintype K] [Nonempty K] [Fintype X]
    [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype S] [Nonempty S] (F : K → X → Y)
    (D : S → OracleComp X Y Bool) (hD : ∀ s O O', (D s).run O = (D s).run O') :
    PRF.prfAdvantage F D = 0 := by
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hreal : PRF.prfReal F D =
      (Cslib.Probability.PMF.uniformOfFintype S).map fun s => (D s).run fun _ => y₀ := by
    rw [PRF.prfReal]
    exact (congrArg (PMF.map · _) (funext fun ω : K × S => hD ω.2 _ _)).trans
      (map_snd_uniformOfFintype (Ω := K) fun s => (D s).run fun _ => y₀)
  have hrand : PRF.prfRand D =
      (Cslib.Probability.PMF.uniformOfFintype S).map fun s => (D s).run fun _ => y₀ := by
    rw [PRF.prfRand]
    exact (congrArg (PMF.map · _) (funext fun ω : (X → Y) × S => hD ω.2 _ _)).trans
      (map_snd_uniformOfFintype (Ω := X → Y) fun s => (D s).run fun _ => y₀)
  rw [PRF.prfAdvantage, hreal, hrand, sub_self, abs_zero]

/-- The constant keyed function on one key, with outputs in `ZMod 2`. -/
def constKey (_ : ℕ) (_ : Unit) (_ : Unit) : ZMod 2 := 0

/-- One key and two outputs: the generator at one point expands, and it is `PRGSecure` against the
distinguishers that ignore their input. -/
example : PRGSecure (fun n => prgOfPRF (constKey n) (fun _ : Fin 1 => ())) (fun _ => Unit)
    (fun D => (∀ n y y' r, (D n).guess y r = (D n).guess y' r) ∧
      ∀ n, (D n).coins = Cslib.Probability.PMF.uniformOfFintype Unit) :=
  prgSecure_prgOfPRF constKey (ℓ := fun _ => 1) (fun _ => fun _ _ _ => Subsingleton.elim _ _)
    (fun _ => by simp) _ (fun B => ∀ n r O O', (B n r).run O = (B n r).run O')
    (fun _ hD => hD.2)
    (fun D hD n r O O' => by rw [run_prgOfPRFReduction, run_prgOfPRFReduction, hD.1 n])
    (fun B hB => negligibleAdv_zero.mono fun n =>
      (prfAdvantage_of_blind (constKey n) (B n) (hB n)).le)

end Cslib.Crypto.PRGFromPRFTests
