/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.Normed.Lp.Finsupp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Finsupp.SMul

/-!
# The L¹ norm on finitely supported families

For any index type ι and normed additive commutative group E, finitely
supported families ι →₀ E with the WithLp 1 metric have norm
∑ i ∈ support(a), ‖a_i‖. Their distance is the sum of coordinate distances
over a finite set containing both supports. These formulas retain the
pointwise additive operations and the L¹ metric.

If E is a normed space over a normed field 𝕜, pointwise scalar multiplication
makes this same finite-support carrier a normed 𝕜-space. Empty index types
and zero support are included.
-/

public section

noncomputable section

open scoped NNReal

universe u v w

namespace Finsupp

variable {ι : Type u} {E : Type v}

local instance : Fact ((1 : ℝ≥0) ≤ 1) := ⟨le_rfl⟩

/-- Let ι be an index type and E a normed additive commutative group.
For finitely supported a,b in WithLp 1 and a finite set s containing both
supports, dist(a,b) = ∑ i ∈ s, dist(a_i,b_i). -/
private theorem l1DistOnSupport [NormedAddCommGroup E]
    (a b : WithLp (1 : ℝ≥0) (ι →₀ E)) (s : Finset ι)
    (ha : a.ofLp.support ⊆ s) (hb : b.ofLp.support ⊆ s) :
    dist a b = ∑ i ∈ s, dist (a.ofLp i) (b.ofLp i) := by
  classical
  rw [Finsupp.dist_def]
  simp only [NNReal.coe_one, inv_one, Real.rpow_one]
  rw [Finsupp.sum_of_support_subset (s := s) _
    ((Finsupp.support_zipWith).trans (Finset.union_subset ha hb)) _ (by simp)]
  simp only [Finsupp.zipWith_apply]

/-- For any index type ι, normed additive commutative group E, and
a,b,c : WithLp 1 (ι →₀ E), dist(c+a,c+b) = dist(a,b) for the L¹ metric. -/
theorem l1_dist_add_left [NormedAddCommGroup E]
    (a b c : WithLp (1 : ℝ≥0) (ι →₀ E)) :
    dist (c + a) (c + b) = dist a b := by
  classical
  let s := c.ofLp.support ∪ a.ofLp.support ∪ b.ofLp.support
  have hc : c.ofLp.support ⊆ s :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have ha : a.ofLp.support ⊆ s :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hb : b.ofLp.support ⊆ s := Finset.subset_union_right
  have hca : (c + a).ofLp.support ⊆ s := by
    simpa only [WithLp.ofLp_add] using
      Finsupp.support_add.trans (Finset.union_subset hc ha)
  have hcb : (c + b).ofLp.support ⊆ s := by
    simpa only [WithLp.ofLp_add] using
      Finsupp.support_add.trans (Finset.union_subset hc hb)
  rw [l1DistOnSupport (c + a) (c + b) s hca hcb,
    l1DistOnSupport a b s ha hb]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [WithLp.ofLp_add, Finsupp.add_apply, dist_add_left]

/-- For any index type ι and normed additive commutative group E,
this is the L¹ metric on WithLp 1 (ι →₀ E). -/
abbrev l1Metric [NormedAddCommGroup E] :
    MetricSpace (WithLp (1 : ℝ≥0) (ι →₀ E)) := inferInstance

/-- For any index type ι and normed additive commutative group E,
the L¹ norm of a finitely supported family a is its L¹ distance from zero,
equal to the finite sum of the coordinate norms. -/
instance instL1Norm [NormedAddCommGroup E] : Norm (WithLp (1 : ℝ≥0) (ι →₀ E)) where
  norm x := dist 0 x

/-- For any index type ι and normed additive commutative group E,
WithLp 1 (ι →₀ E) is a normed additive commutative group with pointwise
addition and the L¹ metric. -/
instance instL1NormedAddCommGroup [NormedAddCommGroup E] :
    NormedAddCommGroup (WithLp (1 : ℝ≥0) (ι →₀ E)) :=
  NormedAddCommGroup.ofAddDist (fun _ => rfl)
    (fun x y z => le_of_eq (l1_dist_add_left x y z).symm)

/-- For any index type ι and normed additive commutative group E,
the metric of the L¹ normed group on WithLp 1 (ι →₀ E) equals its L¹ metric. -/
private theorem l1NormedAddCommGroupMetricComputed [NormedAddCommGroup E] :
    (instL1NormedAddCommGroup (ι := ι) (E := E)).toMetricSpace =
      l1Metric (ι := ι) (E := E) := rfl

/-- For any index type ι and normed additive commutative group E,
the metric induced by the L¹ normed additive structure on
WithLp 1 (ι →₀ E) is exactly l1Metric. -/
theorem l1NormedAddCommGroup_metric_eq [NormedAddCommGroup E] :
    (instL1NormedAddCommGroup (ι := ι) (E := E)).toMetricSpace =
      l1Metric (ι := ι) (E := E) := l1NormedAddCommGroupMetricComputed

/-- For any index type ι, normed additive commutative group E, finitely supported
a : WithLp 1 (ι →₀ E), and finite s containing its support,
‖a‖ = ∑ i ∈ s, ‖a_i‖. -/
private theorem l1NormOnSupport [NormedAddCommGroup E]
    (a : WithLp (1 : ℝ≥0) (ι →₀ E)) (s : Finset ι) (ha : a.ofLp.support ⊆ s) :
    ‖a‖ = ∑ i ∈ s, ‖a.ofLp i‖ := by
  change dist (0 : WithLp (1 : ℝ≥0) (ι →₀ E)) a = _
  rw [l1DistOnSupport 0 a s (by simp) ha]
  simp only [WithLp.ofLp_zero, Finsupp.zero_apply, dist_zero_left]

/-- For any index type ι, normed additive commutative group E, and
a : WithLp 1 (ι →₀ E), its norm is ∑ i ∈ support(a), ‖a_i‖. -/
theorem l1_norm_eq_sum [NormedAddCommGroup E]
    (a : WithLp (1 : ℝ≥0) (ι →₀ E)) :
    ‖a‖ = a.ofLp.sum (fun _ x => ‖x‖) := by
  classical
  exact l1NormOnSupport a a.ofLp.support (by rfl)

variable {𝕜 : Type w} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let 𝕜 be a normed field, E a normed 𝕜-space, and ι any index type.
For r : 𝕜 and a : WithLp 1 (ι →₀ E), ‖r • a‖ = ‖r‖ · ‖a‖. -/
theorem l1_norm_smul (r : 𝕜) (a : WithLp (1 : ℝ≥0) (ι →₀ E)) :
    ‖r • a‖ = ‖r‖ * ‖a‖ := by
  classical
  have hsupport : (r • a).ofLp.support ⊆ a.ofLp.support := by
    simpa only [WithLp.ofLp_smul] using (Finsupp.support_smul (b := r) (g := a.ofLp))
  rw [l1NormOnSupport (r • a) a.ofLp.support hsupport,
    l1NormOnSupport a a.ofLp.support (by rfl), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [WithLp.ofLp_smul, Finsupp.smul_apply, norm_smul]

/-- For a normed field 𝕜, normed 𝕜-space E, and arbitrary index type ι,
the pointwise scalar action on WithLp 1 (ι →₀ E) gives a normed 𝕜-space
with its L¹ norm and metric. -/
instance instL1NormedSpace : NormedSpace 𝕜 (WithLp (1 : ℝ≥0) (ι →₀ E)) where
  norm_smul_le r a := le_of_eq (l1_norm_smul r a)

end Finsupp
