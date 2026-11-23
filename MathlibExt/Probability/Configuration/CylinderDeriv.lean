/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ProductMeasure
public import MathlibExt.Probability.CorrelationInequalities.Russo

/-!
# Cylinder events under Bernoulli product measures

An event of `ConfigSpace E` that depends only on the coordinates in a finite set `F` is the
cylinder over its projection `F.restrict '' A`. Its probability under the infinite Bernoulli
product measure equals the finite-volume weight `prob p (F.restrict '' A)` of the projection, a
polynomial in `p`. Russo's formula on the finite cube therefore applies: the derivative in `p` of
the probability of an increasing cylinder event is the expected number of pivotal coordinates.

## Main definitions

* `StatMech.extendOff F ω η`: the configuration equal to `η` on `F` and to `ω` off `F`.

## Main results

* `StatMech.finiteRealProb_eq_prob`: on a finite index set, the Bernoulli product measure of an
  event is its weight `prob p`.
* `StatMech.realProb_cylinder_eq_prob`, `StatMech.realProb_cylinder_eq_finsum`: the probability
  of an event depending on finitely many coordinates.
* `StatMech.differentiable_realProb_cylinder`: this probability is differentiable in `p`.
* `StatMech.hasDerivAt_realProb_cylinder_pivotal`, `StatMech.deriv_realProb_cylinder_pivotal`:
  Russo's formula for increasing cylinder events.

## References

* L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981),
  229–237.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal

namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]

/-- The mass of a point under the Bernoulli distribution: `p` at `true`, `1 - p` at `false`. -/
lemma bernoulliMeasure_real_singleton (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    (bernoulliMeasure p hp).real {b} = if b then (p : ℝ) else 1 - p := by
  cases b with
  | true => rw [Measure.real, bernoulliMeasure_apply_true]; simp
  | false =>
      rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal, NNReal.coe_sub hp]
      simp

omit [Countable E] [DecidableEq E] in
/-- On a finite index set, the mass of a configuration is its product weight `configWeight`. -/
lemma realSingleton_eq_configWeight [Fintype E] (p : ℝ≥0) (hp : p ≤ 1)
    (ω : ConfigSpace E) :
    (bernoulliProductMeasure (E := E) p hp).real {ω} = configWeight (p : ℝ) ω := by
  rw [bernoulliProductMeasure.real_singleton]
  unfold configWeight edgeWeight
  exact Finset.prod_congr rfl (fun e _ => bernoulliMeasure_real_singleton p hp (ω e))

omit [Countable E] in
/-- On a finite index set, the Bernoulli product measure of an event is its weight `prob p`. -/
lemma finiteRealProb_eq_prob [Fintype E] (p : ℝ≥0) (hp : p ≤ 1)
    (S : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real S = prob (p : ℝ) S := by
  rw [bernoulliProductMeasure.real_eq_sum]
  unfold prob
  exact Finset.sum_congr rfl
    (fun ω _ => by rw [realSingleton_eq_configWeight p hp ω])

/-- The configuration that agrees with `η` on the finite set `F` and with `ω` off `F`. -/
noncomputable def extendOff (F : Finset E) (ω : ConfigSpace E) (η : ConfigSpace ↥F) :
    ConfigSpace E := fun j => if h : j ∈ F then η ⟨j, h⟩ else ω j

omit [Countable E] in
@[simp] lemma restrict_extendOff (F : Finset E) (ω : ConfigSpace E) (η : ConfigSpace ↥F) :
    F.restrict (extendOff F ω η) = η := by
  funext j; simp [Finset.restrict, extendOff, j.2]

omit [Countable E] [DecidableEq E] in
/-- An event whose indicator depends only on the coordinates in `F` is the cylinder over its
projection onto `F`. -/
lemma eq_cylinder_restrict_image (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
    A = cylinder F (F.restrict '' A) := by
  ext ω
  simp only [mem_cylinder, Set.mem_image]
  refine ⟨fun hω => ⟨ω, hω, rfl⟩, ?_⟩
  rintro ⟨ω', hω', heq⟩
  have hind : A.indicator (fun _ => (1 : ℝ)) ω' = A.indicator (fun _ => (1 : ℝ)) ω := by
    refine hA fun i hi => ?_
    have := congrFun heq ⟨i, hi⟩
    simpa [Finset.restrict] using this
  rw [Set.indicator_of_mem hω'] at hind
  by_contra hcon
  rw [Set.indicator_of_notMem hcon] at hind
  norm_num at hind

omit [DecidableEq E] in
/-- The infinite Bernoulli product measure of a cylinder over `F` is the finite Bernoulli product
measure of its base. -/
lemma bernoulliProductMeasure_cylinder (p : ℝ≥0) (hp : p ≤ 1) (F : Finset E)
    (S : Set (ConfigSpace ↥F)) :
    bernoulliProductMeasure (E := E) p hp (cylinder F S)
      = bernoulliProductMeasure (E := ↥F) p hp S := by
  unfold bernoulliProductMeasure
  rw [Measure.infinitePi_cylinder (μ := fun _ : E => bernoulliMeasure p hp) (s := F) (S := S)
        (by measurability),
      ← Measure.infinitePi_eq_pi]

omit [DecidableEq E] in
/-- Real-valued form of `bernoulliProductMeasure_cylinder`. -/
lemma realProb_cylinder (p : ℝ≥0) (hp : p ≤ 1) (F : Finset E)
    (S : Set (ConfigSpace ↥F)) :
    (bernoulliProductMeasure (E := E) p hp).real (cylinder F S)
      = (bernoulliProductMeasure (E := ↥F) p hp).real S := by
  rw [Measure.real, Measure.real, bernoulliProductMeasure_cylinder]

/-- The probability of an event depending only on the coordinates in `F` is the finite weight
`prob p` of its projection onto `F`. -/
theorem realProb_cylinder_eq_prob (p : ℝ≥0) (hp : p ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
      = prob (p : ℝ) (F.restrict '' A) := by
  conv_lhs => rw [eq_cylinder_restrict_image A F hA]
  rw [realProb_cylinder, finiteRealProb_eq_prob]

/-- The probability of an event depending only on the coordinates in `F`, as an explicit
polynomial in `p`. -/
theorem realProb_cylinder_eq_finsum (p : ℝ≥0) (hp : p ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
      = ∑ η : ConfigSpace ↥F,
          (F.restrict '' A).indicator (fun _ => (1 : ℝ)) η
            * ∏ e : ↥F, (if η e then (p : ℝ) else 1 - p) := by
  rw [realProb_cylinder_eq_prob p hp A F hA]
  unfold prob configWeight edgeWeight
  rfl

omit [Countable E] in
/-- The weight of the projection of an event onto finitely many coordinates is differentiable
in `p`. -/
theorem differentiable_realProb_cylinder
    (A : Set (ConfigSpace E)) (F : Finset E) :
    Differentiable ℝ (fun q => prob q (F.restrict '' A)) :=
  fun q => (hasDerivAt_prob (F.restrict '' A) q).differentiableAt

omit [Countable E] [DecidableEq E] in
/-- The projection of an increasing event onto finitely many coordinates is increasing. -/
lemma isIncreasing_restrict_image (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (F : Finset E) : IsIncreasing (F.restrict '' A) := by
  classical
  intro η η' hηη' hη
  obtain ⟨ω, hωA, rfl⟩ := hη
  refine ⟨extendOff F ω η', hA (fun j => ?_) hωA, restrict_extendOff F ω η'⟩
  by_cases hj : j ∈ F
  · simpa [extendOff, hj, Finset.restrict] using hηη' ⟨j, hj⟩
  · simp [extendOff, hj]

omit [Countable E] in
/-- **Russo's formula** for an increasing event `A` projected onto finitely many coordinates `F`:
the derivative in `p` of its weight is the sum over `e ∈ F` of the weight of the event that `e`
is pivotal (L. Russo, 1981). -/
theorem hasDerivAt_realProb_cylinder_pivotal
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (F : Finset E) (q : ℝ) :
    HasDerivAt (fun q => prob q (F.restrict '' A))
      (∑ e : ↥F, pivotalProb q (F.restrict '' A) e) q :=
  hasDerivAt_prob_eq_sum_pivotalProb (F.restrict '' A) (isIncreasing_restrict_image A hA F) q

omit [Countable E] in
/-- **Russo's formula**, `deriv` form of `hasDerivAt_realProb_cylinder_pivotal`. -/
theorem deriv_realProb_cylinder_pivotal
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (F : Finset E) (q : ℝ) :
    deriv (fun q => prob q (F.restrict '' A)) q
      = ∑ e : ↥F, pivotalProb q (F.restrict '' A) e :=
  (hasDerivAt_realProb_cylinder_pivotal A hA F q).deriv

end StatMech
