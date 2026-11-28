/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.OnlineClassification

/-!
# Online classification tests

* Boundary cases: on the empty sequence a learner makes no mistakes and has regret `0`, and
  against the empty class the regret is the expected number of mistakes.
* The halving run of `HalvingTests`: on `[(false, true), (true, true)]` over the four Boolean
  functions of one Boolean variable, halving errs twice, by evaluation of `mistakes` and through
  `halvingMistakes_eq_mistakes`; as a randomized learner it has the same expected number of
  mistakes, and its regret against the class is `2`, as the sequence is realizable.
* The fair coin `p_t = 1/2` against the two constant hypotheses, the class of Cover's example in
  Section 21.2 of Shalev-Shwartz and Ben-David: on `[((), true), ((), false)]` the coin expects
  one mistake, each hypothesis makes one, and the regret is `0`; the number of rounds with
  `p_t ≠ y_t` is `2`, larger than the expected number of mistakes.
* The expected number of mistakes of the coin on one round, as an integral over the Bernoulli
  prediction, is `1/2`.
-/

@[expose] public section

namespace Cslib.MachineLearning.OnlineClassificationTests

open Cslib.MachineLearning.OnlineClassification Cslib.MachineLearning.Halving
open MeasureTheory ProbabilityTheory unitInterval

/-! ### Boundary cases -/

example {X : Type*} (A : List (X × Bool) → X → I) (H : Set (X → Bool)) : regret A H [] = 0 := by
  simp only [regret, expectedMistakes_nil, mistakes_nil, zero_sub, neg_eq_zero, Nat.cast_eq_zero]
  rcases H.eq_empty_or_nonempty with rfl | ⟨h, hh⟩
  · simp
  · exact Nat.sInf_eq_zero.2 (Or.inl ⟨h, hh, rfl⟩)

example {X : Type*} (A : List (X × Bool) → X → I) (S : List (X × Bool)) :
    regret A ∅ S = expectedMistakes A S := by
  simp [regret]

/-! ### The halving run -/

/-- The four Boolean functions of one Boolean variable. -/
def C : Finset (Bool → Bool) := {id, not, fun _ => true, fun _ => false}

/-- The examples `(false, true), (true, true)`, labeled by `const true`. -/
def S : List (Bool × Bool) := [(false, true), (true, true)]

example : mistakes (halvingPredict C) S = 2 := by decide

example : halvingMistakes C [] S = 2 := by
  rw [halvingMistakes_eq_mistakes]
  decide

theorem realizable_S :
    PACLearning.Realizable (C : Set (Bool → Bool)) (fun t : Fin S.length => S[t]) :=
  (realizable_iff _ _).2 ⟨fun _ => true, by simp [C], by decide⟩

example : expectedMistakes (fun s x => if halvingPredict C s x then 1 else 0) S = 2 := by
  rw [expectedMistakes_ofBool]
  norm_num [show mistakes (halvingPredict C) S = 2 by decide]

example : regret (fun s x => if halvingPredict C s x then 1 else 0) C S = 2 := by
  rw [regret_of_realizable _ realizable_S, expectedMistakes_ofBool]
  norm_num [show mistakes (halvingPredict C) S = 2 by decide]

/-! ### The fair coin against the constant hypotheses -/

/-- The fair coin, `p = 1/2`. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Two rounds on a single instance, labeled `true` and then `false`. -/
def S' : List (Unit × Bool) := [((), true), ((), false)]

/-- The two constant hypotheses. -/
def H' : Set (Unit → Bool) := {fun _ => true, fun _ => false}

theorem expectedMistakes_half : expectedMistakes (fun _ _ => half) S' = 1 := by
  change ∑ t : Fin 2, |((half : I) : ℝ) - (S'[t].2.toNat : ℝ)| = 1
  rw [Fin.sum_univ_two]
  norm_num [S', half, abs_of_neg]

theorem mistakes_const_S' (b : Bool) : mistakes (fun _ _ => b) S' = 1 := by
  cases b <;> decide

example : regret (fun _ _ => half) H' S' = 0 := by
  obtain ⟨h, hh, he⟩ := exists_regret_eq (H := H') (fun _ _ => half) S' ⟨fun _ => true, Or.inl rfl⟩
  rw [he, expectedMistakes_half]
  rcases hh with rfl | rfl
  · rw [mistakes_const_S' true]; norm_num
  · rw [mistakes_const_S' false]; norm_num

example : expectedMistakes (fun _ _ => half) S' <
    ∑ t : Fin S'.length, if ((half : I) : ℝ) = S'[t].2.toNat then 0 else 1 :=
  expectedMistakes_lt _ _ ⟨⟨0, by decide⟩, by norm_num [half]⟩

/-! ### The expectation over the Bernoulli prediction -/

example :
    ∫ ŷ, (∑ t : Fin 1, if ŷ t = ([((), true)] : List (Unit × Bool))[t].2 then (0 : ℝ) else 1)
        ∂Measure.pi (fun _ : Fin 1 => Ber(true, false, half)) = 1 / 2 := by
  refine (integral_mistakes_eq_expectedMistakes (fun _ _ => half) [((), true)]).trans ?_
  change ∑ t : Fin 1, |((half : I) : ℝ) - (([((), true)] : List (Unit × Bool))[t].2.toNat : ℝ)| =
    1 / 2
  norm_num [half, abs_of_neg]

end Cslib.MachineLearning.OnlineClassificationTests
