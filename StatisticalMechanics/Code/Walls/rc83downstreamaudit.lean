/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Inequalities.Reimer
import Code.Sharpness.BkCriterion

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace
open StatMech.Sharpness

variable {E : Type*}







theorem rc83_bk_increasing [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  bk_inequality hp hA hB




theorem rc83_disjointOccurrence_increasing {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    IsIncreasing (disjointOccurrence A B) :=
  disjointOccurrence_isIncreasing hA hB





theorem rc83_bk_triple_increasing [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {P Q R : Set (ConfigSpace E)} (hP : IsIncreasing P) (hQ : IsIncreasing Q)
    (hR : IsIncreasing R) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence P (disjointOccurrence Q R))
      ≤ (bernoulliProductMeasure (E := E) p hp).real P
        * (bernoulliProductMeasure (E := E) p hp).real Q
        * (bernoulliProductMeasure (E := E) p hp).real R :=
  bk_triple hp hP hQ hR









theorem rc83_reimer_not_needed_for_increasing [Fintype E] [DecidableEq E] {p : ℝ≥0}
    (hp : p ≤ 1) {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  bk_inequality hp hA hB






theorem rc83_reimer_core_of_increasing_would_follow
    (n : ℕ) (φ : Fin n → Bool → ℝ)
    (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin n))) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  reimerCore_holds_on_increasing n φ hφ0 hφ1 A B hA hB










theorem rc83_connEvent_triple_increasing_witness {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V) (u : V) (x y : V) (A B : Set V) :
    IsIncreasing (disjointOccurrence (connEvent G S u {x})
      (disjointOccurrence (edgeOpenEvent x y) (connEvent G A y B))) :=
  rc83_disjointOccurrence_increasing (isIncreasing_connEvent G S u {x})
    (rc83_disjointOccurrence_increasing (isIncreasing_edgeOpenEvent x y)
      (isIncreasing_connEvent G A y B))









theorem rc83_downstream_audit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {p : ℝ≥0} (hp : p ≤ 1) (S : Set V) (u : V) (x y : V) (A B : Set V) :
    (∀ (P Q R : Set (ConfigSpace (Sym2 V))),
        IsIncreasing P → IsIncreasing Q → IsIncreasing R →
        (bernoulliProductMeasure (E := Sym2 V) p hp).real
            (disjointOccurrence P (disjointOccurrence Q R))
          ≤ (bernoulliProductMeasure (E := Sym2 V) p hp).real P
            * (bernoulliProductMeasure (E := Sym2 V) p hp).real Q
            * (bernoulliProductMeasure (E := Sym2 V) p hp).real R)
      ∧ IsIncreasing (disjointOccurrence (connEvent G S u {x})
          (disjointOccurrence (edgeOpenEvent x y) (connEvent G A y B))) :=
  ⟨fun _ _ _ hP hQ hR => rc83_bk_triple_increasing hp hP hQ hR,
   rc83_connEvent_triple_increasing_witness G S u x y A B⟩

end StatMech
