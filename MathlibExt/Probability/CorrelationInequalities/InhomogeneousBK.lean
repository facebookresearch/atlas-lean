/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.InfiniteBK

@[expose] public section

/-!
# BK inequality for inhomogeneous Bernoulli product measures

`inhomBernoulliProductMeasure p` is the product measure on `ConfigSpace E` under which coordinate
`e` is open with probability `p e`. The BK inequality holds for it: on a finite set directly from
`StatMech.bk_wprob_general`, and on a countable set for increasing events depending on finitely
many coordinates.

## Main definitions

* `StatMech.inhomBernoulliProductMeasure p hp`: the product of `bernoulliMeasure (p e)`. For
  constant `p` it is `bernoulliProductMeasure` (`StatMech.inhomBernoulliProductMeasure_const`).

## Main results

* `StatMech.inhom_bk_inequality`: the BK inequality on a finite set.
* `StatMech.inhom_bk_of_finite_dependsOn`, `StatMech.inhom_bk_triple_of_finite_dependsOn`,
  `StatMech.inhom_bk_criterion_of_finite_dependsOn`: the countable case, the three-event form,
  and the resulting union bound.
* `StatMech.inhom_coord_true_prob`: coordinate `e` is open with probability `p e`.

## References

* J. van den Berg, H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatMech

variable {E : Type*}

/-- The product measure on `ConfigSpace E` under which coordinate `e` is open (`true`) with
probability `p e`, independently. -/
noncomputable def inhomBernoulliProductMeasure (p : E → ℝ≥0)
    (hp : ∀ e, p e ≤ 1) : Measure (ConfigSpace E) :=
  Measure.infinitePi (fun e => bernoulliMeasure (p e) (hp e))

/-- The inhomogeneous Bernoulli product measure is a probability measure. -/
instance (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) :
    IsProbabilityMeasure (inhomBernoulliProductMeasure p hp) := by
  unfold inhomBernoulliProductMeasure
  infer_instance

/-- For a constant parameter, the inhomogeneous product is `bernoulliProductMeasure`. -/
theorem inhomBernoulliProductMeasure_const (p : ℝ≥0) (hp : p ≤ 1) :
    inhomBernoulliProductMeasure (E := E) (fun _ => p) (fun _ => hp)
      = bernoulliProductMeasure p hp := rfl

namespace inhomBernoulliProductMeasure

variable {p : E → ℝ≥0} {hp : ∀ e, p e ≤ 1}

theorem apply_singleton [Fintype E] (omega : ConfigSpace E) :
    inhomBernoulliProductMeasure p hp {omega} =
      ∏ e, bernoulliMeasure (p e) (hp e) {omega e} := by
  unfold inhomBernoulliProductMeasure
  rw [Measure.infinitePi_singleton_of_fintype]

theorem real_singleton [Fintype E] (omega : ConfigSpace E) :
    (inhomBernoulliProductMeasure p hp).real {omega} =
      ∏ e, (bernoulliMeasure (p e) (hp e)).real {omega e} := by
  rw [Measure.real, apply_singleton, ENNReal.toReal_prod]
  rfl

theorem real_eq_sum [Fintype E] [DecidableEq E]
    (A : Set (ConfigSpace E)) :
    (inhomBernoulliProductMeasure p hp).real A =
      ∑ omega : ConfigSpace E,
        A.indicator (fun _ => (1 : ℝ)) omega *
          (inhomBernoulliProductMeasure p hp).real {omega} := by
  classical
  set mu := inhomBernoulliProductMeasure p hp with hmu
  have key : mu.real A =
      ∑ omega ∈ Finset.univ.filter (· ∈ A), mu.real {omega} := by
    have hsum : mu A = ∑ omega ∈ Finset.univ.filter (· ∈ A), mu {omega} := by
      rw [sum_measure_singleton]
      congr 1
      ext omega
      simp
    rw [Measure.real, hsum,
      ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    rfl
  rw [key, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun omega _ => ?_)
  by_cases h : omega ∈ A
  · rw [ite_eq_left h, Set.indicator_of_mem h]
    ring
  · rw [ite_eq_right h, Set.indicator_of_notMem h]
    ring

end inhomBernoulliProductMeasure

theorem inhom_real_eq_wprob [Fintype E] [DecidableEq E]
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) (A : Set (ConfigSpace E)) :
    (inhomBernoulliProductMeasure p hp).real A =
      wprob (fun e b => (bernoulliMeasure (p e) (hp e)).real {b}) A := by
  rw [inhomBernoulliProductMeasure.real_eq_sum]
  apply Finset.sum_congr rfl
  intro omega _
  rw [inhomBernoulliProductMeasure.real_singleton]
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The **BK inequality** for an inhomogeneous Bernoulli product measure on a finite set. -/
theorem inhom_bk_inequality [Fintype E] [DecidableEq E]
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (inhomBernoulliProductMeasure p hp).real (disjointOccurrence A B) ≤
      (inhomBernoulliProductMeasure p hp).real A *
        (inhomBernoulliProductMeasure p hp).real B := by
  let phi : E → Bool → ℝ :=
    fun e b => (bernoulliMeasure (p e) (hp e)).real {b}
  have hphi0 : ∀ e b, 0 ≤ phi e b := fun _ _ => measureReal_nonneg
  have hphi1 : ∀ e, phi e false + phi e true = 1 := fun e =>
    bernoulliMeasure_real_false_add_true (hp e)
  rw [inhom_real_eq_wprob p hp (disjointOccurrence A B),
    inhom_real_eq_wprob p hp A, inhom_real_eq_wprob p hp B]
  exact bk_wprob_general phi hphi0 hphi1 hA hB

variable [Countable E] [DecidableEq E]

omit [DecidableEq E] in
theorem inhom_realProb_cylinder (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (F : Finset E) (A : Set (ConfigSpace F)) :
    (inhomBernoulliProductMeasure p hp).real (MeasureTheory.cylinder F A) =
      (inhomBernoulliProductMeasure (fun e : F => p e)
        (fun e => hp e)).real A := by
  classical
  unfold inhomBernoulliProductMeasure
  rw [Measure.real, Measure.real,
    Measure.infinitePi_cylinder
      (μ := fun e : E => bernoulliMeasure (p e) (hp e))
      (s := F) (S := A) (by measurability),
    ← Measure.infinitePi_eq_pi]

omit [Countable E] [DecidableEq E] in
theorem inhom_coord_true_prob (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) (e : E) :
    (inhomBernoulliProductMeasure p hp).real {omega | omega e = true} =
      (p e : ℝ) := by
  classical
  have hmarg :
      Measure.map (fun omega : ConfigSpace E => omega e)
          (inhomBernoulliProductMeasure p hp) =
        bernoulliMeasure (p e) (hp e) := by
    unfold inhomBernoulliProductMeasure
    exact Measure.infinitePi_map_eval
      (fun i : E => bernoulliMeasure (p i) (hp i)) e
  have happ :
      inhomBernoulliProductMeasure p hp {omega | omega e = true} =
        bernoulliMeasure (p e) (hp e) {true} := by
    rw [← hmarg, Measure.map_apply (measurable_pi_apply e)
      (measurableSet_singleton true)]
    rfl
  rw [Measure.real, happ, bernoulliMeasure_apply_true, ENNReal.coe_toReal]

omit [DecidableEq E] in
/-- The BK inequality for an inhomogeneous Bernoulli product measure on a countable set, for
increasing events depending on finitely many coordinates. -/
theorem inhom_bk_of_finite_dependsOn (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    {A B : Set (ConfigSpace E)} (F : Finset E)
    (hAdep : DependsOn A (F : Set E)) (hBdep : DependsOn B (F : Set E))
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) :
    (inhomBernoulliProductMeasure p hp).real (disjointOccurrence A B) ≤
      (inhomBernoulliProductMeasure p hp).real A *
        (inhomBernoulliProductMeasure p hp).real B := by
  classical
  have hDOdep := ibk_disjointOccurrence_dependsOn hAdep hBdep
  have hDOrw := ih_eq_cylinder_of_dependsOn F hDOdep
  have hArw := ih_eq_cylinder_of_dependsOn F hAdep
  have hBrw := ih_eq_cylinder_of_dependsOn F hBdep
  have hDOprob :
      (inhomBernoulliProductMeasure p hp).real (disjointOccurrence A B) =
        (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real
          (ih_section (disjointOccurrence A B) F) := by
    calc
      (inhomBernoulliProductMeasure p hp).real (disjointOccurrence A B) =
          (inhomBernoulliProductMeasure p hp).real
            (MeasureTheory.cylinder F (ih_section (disjointOccurrence A B) F)) :=
        congrArg (inhomBernoulliProductMeasure p hp).real hDOrw
      _ = _ := inhom_realProb_cylinder p hp F _
  have hAprob :
      (inhomBernoulliProductMeasure p hp).real A =
        (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real
          (ih_section A F) := by
    calc
      (inhomBernoulliProductMeasure p hp).real A =
          (inhomBernoulliProductMeasure p hp).real
            (MeasureTheory.cylinder F (ih_section A F)) :=
        congrArg (inhomBernoulliProductMeasure p hp).real hArw
      _ = _ := inhom_realProb_cylinder p hp F _
  have hBprob :
      (inhomBernoulliProductMeasure p hp).real B =
        (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real
          (ih_section B F) := by
    calc
      (inhomBernoulliProductMeasure p hp).real B =
          (inhomBernoulliProductMeasure p hp).real
            (MeasureTheory.cylinder F (ih_section B F)) :=
        congrArg (inhomBernoulliProductMeasure p hp).real hBrw
      _ = _ := inhom_realProb_cylinder p hp F _
  calc
    (inhomBernoulliProductMeasure p hp).real (disjointOccurrence A B) =
        (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real
          (ih_section (disjointOccurrence A B) F) := hDOprob
    _ ≤ (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real
          (disjointOccurrence (ih_section A F) (ih_section B F)) :=
      measureReal_mono (ibk_section_disjointOccurrence_subset A B F)
    _ ≤ (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real
          (ih_section A F) *
        (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real
          (ih_section B F) :=
      inhom_bk_inequality _ _ (ih_section_isIncreasing hAinc F)
        (ih_section_isIncreasing hBinc F)
    _ = (inhomBernoulliProductMeasure p hp).real A *
          (inhomBernoulliProductMeasure p hp).real B :=
      (congrArg₂ (· * ·) hAprob hBprob).symm

omit [DecidableEq E] in
theorem inhom_bk_triple_of_finite_dependsOn (p : E → ℝ≥0)
    (hp : ∀ e, p e ≤ 1) {P Q R : Set (ConfigSpace E)} (F : Finset E)
    (hPdep : DependsOn P (F : Set E)) (hQdep : DependsOn Q (F : Set E))
    (hRdep : DependsOn R (F : Set E))
    (hP : IsIncreasing P) (hQ : IsIncreasing Q) (hR : IsIncreasing R) :
    (inhomBernoulliProductMeasure p hp).real
        (disjointOccurrence P (disjointOccurrence Q R)) ≤
      (inhomBernoulliProductMeasure p hp).real P *
        (inhomBernoulliProductMeasure p hp).real Q *
        (inhomBernoulliProductMeasure p hp).real R := by
  classical
  let mu := inhomBernoulliProductMeasure p hp
  have hQRdep := ibk_disjointOccurrence_dependsOn hQdep hRdep
  calc
    mu.real (disjointOccurrence P (disjointOccurrence Q R)) ≤
        mu.real P * mu.real (disjointOccurrence Q R) :=
      inhom_bk_of_finite_dependsOn p hp F hPdep hQRdep hP
        (disjointOccurrence_isIncreasing hQ hR)
    _ ≤ mu.real P * (mu.real Q * mu.real R) :=
      mul_le_mul_of_nonneg_left
        (inhom_bk_of_finite_dependsOn p hp F hQdep hRdep hQ hR)
        measureReal_nonneg
    _ = mu.real P * mu.real Q * mu.real R := by ring

omit [DecidableEq E] in
theorem inhom_bk_criterion_of_finite_dependsOn {I : Type*}
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (s : Finset I) (P Q R : I → Set (ConfigSpace E)) (F : Finset E)
    (hPdep : ∀ i ∈ s, DependsOn (P i) (F : Set E))
    (hQdep : ∀ i ∈ s, DependsOn (Q i) (F : Set E))
    (hRdep : ∀ i ∈ s, DependsOn (R i) (F : Set E))
    (hP : ∀ i ∈ s, IsIncreasing (P i))
    (hQ : ∀ i ∈ s, IsIncreasing (Q i))
    (hR : ∀ i ∈ s, IsIncreasing (R i))
    {C : Set (ConfigSpace E)}
    (hC : C ⊆ ⋃ i ∈ s,
      disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
    (inhomBernoulliProductMeasure p hp).real C ≤
      ∑ i ∈ s, (inhomBernoulliProductMeasure p hp).real (P i) *
        (inhomBernoulliProductMeasure p hp).real (Q i) *
        (inhomBernoulliProductMeasure p hp).real (R i) := by
  classical
  let mu := inhomBernoulliProductMeasure p hp
  calc
    mu.real C ≤ mu.real
        (⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
      measureReal_mono hC (measure_ne_top _ _)
    _ ≤ ∑ i ∈ s,
        mu.real (disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
      measureReal_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, mu.real (P i) * mu.real (Q i) * mu.real (R i) :=
      Finset.sum_le_sum fun i hi =>
        inhom_bk_triple_of_finite_dependsOn p hp F
          (hPdep i hi) (hQdep i hi) (hRdep i hi)
          (hP i hi) (hQ i hi) (hR i hi)

end StatMech
