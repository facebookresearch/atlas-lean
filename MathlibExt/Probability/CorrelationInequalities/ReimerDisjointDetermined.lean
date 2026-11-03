/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Reimer
public import MathlibExt.Probability.CorrelationInequalities.ReimerCompression

@[expose] public section

/-!
# Events determined by disjoint coordinate sets

If `A` is determined by the coordinates in `K`, `B` by the coordinates in `L`, and `K` and `L`
are disjoint, then `A` and `B` are independent under every product measure, and `A □ B = A ∩ B`.
Hence Reimer's inequality holds for such a pair with equality.

## Main definitions

* `StatMech.DeterminedBy A K`: membership in `A` depends only on the coordinates in `K`. This is
  the same predicate as `StatMech.DependsOn` (`StatMech.determinedBy_iff_dependsOn`).

## Main results

* `StatMech.wprob_inter_eq_mul_of_determined`: events determined by disjoint coordinate sets are
  independent under a product probability weight.
* `StatMech.reimer_bernoulli_eq_of_determinedDisjoint`: for such events,
  `P_p(A □ B) = P_p(A) * P_p(B)` under the product Bernoulli measure.
-/

open MeasureTheory Finset
open scoped NNReal BigOperators

namespace StatMech

open ConfigSpace

variable {E : Type*}

/-- `DeterminedBy A K`: whether a configuration lies in `A` depends only on its values on `K`.
This is definitionally `StatMech.DependsOn A K`. -/
def DeterminedBy (A : Set (ConfigSpace E)) (K : Set E) : Prop :=
  ∀ ω ω' : ConfigSpace E, agreeOn K ω ω' → (ω ∈ A ↔ ω' ∈ A)

/-- `DeterminedBy` and `DependsOn` are the same predicate. -/
lemma determinedBy_iff_dependsOn {A : Set (ConfigSpace E)} {K : Set E} :
    DeterminedBy A K ↔ DependsOn A K := Iff.rfl

/-- Events determined by disjoint coordinate sets are independent under a product probability
weight: `wprob φ (A ∩ B) = wprob φ A * wprob φ B`. -/
theorem wprob_inter_eq_mul_of_determined [Fintype E] [DecidableEq E]
    (A B : Set (ConfigSpace E)) {K L : Set E}
    (hKL : Disjoint K L) (φ : E → Bool → ℝ) (h1 : ∀ x, φ x false + φ x true = 1)
    (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
  classical
  have hL : L ⊆ {x | ¬ (x ∈ K)} := by
    rw [Set.disjoint_left] at hKL
    intro x hx; exact fun hxK => hKL hxK hx
  exact wprob_inter_mul_of_split (fun x => x ∈ K) φ h1 (hA : DependsOn A K)
    (DependsOn.mono (hB : DependsOn B L) hL)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Reimer's inequality with equality for events determined by disjoint coordinate sets: under
the product Bernoulli(`p`) measure, `P_p(A □ B) = P_p(A) * P_p(B)`. -/
theorem reimer_bernoulli_eq_of_determinedDisjoint [Fintype E] [DecidableEq E] {p : ℝ≥0}
    (hp : p ≤ 1) {A B : Set (ConfigSpace E)} {K L : Set E} (hKL : Disjoint K L)
    (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      = (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact reimer_wprob_of_disjoint_support _ (fun _ => bernoulliMeasure_real_false_add_true hp)
    (hA : DependsOn A K) (hB : DependsOn B L) hKL

end StatMech
