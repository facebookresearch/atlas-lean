/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# Nearest-point projection onto a convex set in a real inner product space

Let `K` be a nonempty complete convex subset of a real inner product space `F`.
Every point `x : F` has a nearest point in `K`, and the choice of nearest point
is unique, nonexpansive, and firmly nonexpansive: writing `p` for a nearest point
to `x` and `q` for a nearest point to `y`,

* `‖p - q‖ ≤ ‖x - y‖`, and
* `‖p - q‖ ^ 2 + ‖(x - p) - (y - q)‖ ^ 2 ≤ ‖x - y‖ ^ 2`.

The function `convexProjection K` packages this choice; it is `1`-Lipschitz,
it fixes the points of `K`, and it is idempotent.

This generalizes the v1 book's projection proposition
(`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`, April 22,
2021 section), which is about the projection onto a *closed subspace* and is
already in Mathlib as `orthogonalProjectionOnto` (including its
`1`-Lipschitz property). The convex-set version here is new: Mathlib has the
existence of a nearest point (`exists_norm_eq_iInf_of_complete_convex`) and the
variational characterization
(`norm_eq_iInf_iff_real_inner_le_zero`), both used but not re-ported, and
neither uniqueness, nonexpansiveness, nor firm nonexpansiveness for convex
sets. No completeness hypothesis on `F` itself is needed, only that `K` is
complete. See e.g. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*,
Theorem 5.2.
-/

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.ConvexProjection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- If two points of `K` both satisfy the variational inequality for `x`,
then they are equal: adding the two inequalities gives `‖p - q‖ ^ 2 ≤ 0`. -/
private theorem eq_of_variational {K : Set F} {x p q : F}
    (hp : ∀ w ∈ K, ⟪x - p, w - p⟫_ℝ ≤ 0)
    (hq : ∀ w ∈ K, ⟪x - q, w - q⟫_ℝ ≤ 0)
    (hpK : p ∈ K) (hqK : q ∈ K) : p = q := by
  have h1 := hp q hqK
  have h2 := hq p hpK
  have hsplit : ⟪x - q, p - q⟫_ℝ = ⟪x - p, p - q⟫_ℝ + ‖p - q‖ ^ 2 := by
    have hdecomp : x - q = (x - p) + (p - q) := by abel
    rw [hdecomp, inner_add_left, real_inner_self_eq_norm_sq]
  have hneg : ⟪x - p, p - q⟫_ℝ = -⟪x - p, q - p⟫_ℝ := by
    rw [show p - q = -(q - p) by abel, inner_neg_right]
  have hsq : ‖p - q‖ ^ 2 ≤ 0 := by linarith
  have hsq0 : ‖p - q‖ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  have hnorm : ‖p - q‖ = 0 := sq_eq_zero_iff.mp hsq0
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- A nearest point satisfies the variational inequality. -/
private theorem variational_of_isNearestPoint {K : Set F} (hKv : Convex ℝ K)
    {x p : F} (hpK : p ∈ K) (hp : ‖x - p‖ = ⨅ w : K, ‖x - w‖) :
    ∀ w ∈ K, ⟪x - p, w - p⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hKv hpK).mp hp

/-- Two nearest points to the same `x` are equal. -/
private theorem eq_of_isNearestPoint {K : Set F} (hKv : Convex ℝ K)
    {x p q : F} (hpK : p ∈ K) (hqK : q ∈ K)
    (hp : ‖x - p‖ = ⨅ w : K, ‖x - w‖)
    (hq : ‖x - q‖ = ⨅ w : K, ‖x - w‖) : p = q :=
  eq_of_variational (variational_of_isNearestPoint hKv hpK hp)
    (variational_of_isNearestPoint hKv hqK hq) hpK hqK

/-- **Existence and uniqueness of the nearest point.** A nonempty complete
convex set in a real inner product space has exactly one point nearest to
each `x`. -/
theorem exists_unique_nearest_point_of_complete_convex {K : Set F}
    (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K) (x : F) :
    ∃! p, p ∈ K ∧ ‖x - p‖ = ⨅ w : K, ‖x - w‖ := by
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc hKv x
  exact ⟨p, ⟨hpK, hp⟩, fun q hq =>
    (eq_of_isNearestPoint hKv hpK hq.1 hp hq.2).symm⟩

/-- Totalized existence statement behind `convexProjection`: a point that
is the nearest point whenever `K` satisfies the hypotheses. -/
theorem exists_convexProjection_spec (K : Set F) (x : F) :
    ∃ p : F, (K.Nonempty → IsComplete K → Convex ℝ K →
      p ∈ K ∧ ‖x - p‖ = ⨅ w : K, ‖x - w‖) := by
  by_cases h : K.Nonempty ∧ IsComplete K ∧ Convex ℝ K
  · obtain ⟨p, hpK, hp⟩ :=
      exists_norm_eq_iInf_of_complete_convex h.1 h.2.1 h.2.2 x
    exact ⟨p, fun _ _ _ => ⟨hpK, hp⟩⟩
  · exact ⟨x, fun hne hc hcv => False.elim (h ⟨hne, hc, hcv⟩)⟩

/-- The nearest-point projection onto `K`: for a nonempty complete convex
`K`, `convexProjection K x` is the unique point of `K` nearest to `x`.
Outside those hypotheses its value is unspecified. The properties of this
chosen function below assume them. -/
noncomputable def convexProjection (K : Set F) (x : F) : F :=
  Classical.choose (exists_convexProjection_spec K x)

/-- The projection lies in `K` and attains the infimum of the distances. -/
theorem convexProjection_spec {K : Set F} (hKne : K.Nonempty) (hKc : IsComplete K)
    (hKv : Convex ℝ K) (x : F) :
    convexProjection K x ∈ K ∧ ‖x - convexProjection K x‖ = ⨅ w : K, ‖x - w‖ :=
  Classical.choose_spec (exists_convexProjection_spec K x) hKne hKc hKv

/-- The projection lies in `K`. -/
theorem convexProjection_mem {K : Set F} (hKne : K.Nonempty) (hKc : IsComplete K)
    (hKv : Convex ℝ K) (x : F) : convexProjection K x ∈ K :=
  (convexProjection_spec hKne hKc hKv x).1

/-- The projection attains the infimum of the distances to `K`. -/
theorem convexProjection_norm_eq_iInf {K : Set F} (hKne : K.Nonempty)
    (hKc : IsComplete K) (hKv : Convex ℝ K) (x : F) :
    ‖x - convexProjection K x‖ = ⨅ w : K, ‖x - w‖ :=
  (convexProjection_spec hKne hKc hKv x).2

/-- **Variational characterization of the projection:** `⟪x - P x, w - P x⟫ ≤ 0`
for every `w ∈ K`. -/
theorem convexProjection_variational {K : Set F} (hKne : K.Nonempty)
    (hKc : IsComplete K) (hKv : Convex ℝ K) (x : F) :
    ∀ w ∈ K, ⟪x - convexProjection K x, w - convexProjection K x⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hKv (convexProjection_mem hKne hKc hKv x)).mp
    (convexProjection_norm_eq_iInf hKne hKc hKv x)

/-- Any nearest point equals the projection. -/
theorem convexProjection_eq_of_isNearestPoint {K : Set F} (hKne : K.Nonempty)
    (hKc : IsComplete K) (hKv : Convex ℝ K) {x p : F} (hpK : p ∈ K)
    (hp : ‖x - p‖ = ⨅ w : K, ‖x - w‖) : convexProjection K x = p :=
  eq_of_isNearestPoint hKv (convexProjection_mem hKne hKc hKv x) hpK
    (convexProjection_norm_eq_iInf hKne hKc hKv x) hp

omit [InnerProductSpace ℝ F] in
/-- The infimum of the distances from a point of `K` to `K` is `0`. -/
private theorem iInf_eq_zero_of_mem {K : Set F} {x : F} (hx : x ∈ K) :
    ⨅ w : K, ‖x - w‖ = 0 := by
  let : Nonempty K := ⟨⟨x, hx⟩⟩
  refine le_antisymm ?_ (le_ciInf fun _ => norm_nonneg _)
  have h : (⨅ w : K, ‖x - w‖) ≤ ‖x - (⟨x, hx⟩ : K)‖ :=
    ciInf_le (f := fun w : K => ‖x - (w : F)‖)
      ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩ ⟨x, hx⟩
  simpa using h

/-- The projection fixes every point of `K`. -/
theorem convexProjection_eq_self_of_mem {K : Set F} (hKne : K.Nonempty)
    (hKc : IsComplete K) (hKv : Convex ℝ K) {x : F} (hx : x ∈ K) :
    convexProjection K x = x := by
  apply convexProjection_eq_of_isNearestPoint hKne hKc hKv hx
  rw [sub_self, norm_zero]
  exact (iInf_eq_zero_of_mem hx).symm

/-- The projection is idempotent. -/
theorem convexProjection_idem {K : Set F} (hKne : K.Nonempty) (hKc : IsComplete K)
    (hKv : Convex ℝ K) (x : F) :
    convexProjection K (convexProjection K x) = convexProjection K x :=
  convexProjection_eq_self_of_mem hKne hKc hKv (convexProjection_mem hKne hKc hKv x)

/-- The displacement of two nearest points has nonnegative inner product
with the difference of the residuals; this is the single estimate behind
both nonexpansiveness and firm nonexpansiveness. -/
private theorem inner_sub_sub_nonneg_of_isNearestPoint {K : Set F} (hKv : Convex ℝ K)
    {x y p q : F} (hpK : p ∈ K) (hqK : q ∈ K)
    (hp : ‖x - p‖ = ⨅ w : K, ‖x - w‖)
    (hq : ‖y - q‖ = ⨅ w : K, ‖y - w‖) :
    0 ≤ ⟪(x - p) - (y - q), p - q⟫_ℝ := by
  have h1 := (norm_eq_iInf_iff_real_inner_le_zero hKv hpK).mp hp q hqK
  have h2 := (norm_eq_iInf_iff_real_inner_le_zero hKv hqK).mp hq p hpK
  have hsub : ⟪(x - p) - (y - q), p - q⟫_ℝ
      = ⟪x - p, p - q⟫_ℝ - ⟪y - q, p - q⟫_ℝ := inner_sub_left _ _ _
  have hneg : ⟪x - p, p - q⟫_ℝ = -⟪x - p, q - p⟫_ℝ := by
    rw [show p - q = -(q - p) by abel, inner_neg_right]
  rw [hsub, hneg]
  linarith

/-- **Nonexpansiveness of nearest-point selection:** nearest points to `x`
and `y` are no farther apart than `x` and `y`. -/
theorem norm_sub_le_of_isNearestPoint {K : Set F} (hKv : Convex ℝ K)
    {x y p q : F} (hpK : p ∈ K) (hqK : q ∈ K)
    (hp : ‖x - p‖ = ⨅ w : K, ‖x - w‖)
    (hq : ‖y - q‖ = ⨅ w : K, ‖y - w‖) :
    ‖p - q‖ ≤ ‖x - y‖ := by
  have hinner := inner_sub_sub_nonneg_of_isNearestPoint hKv hpK hqK hp hq
  have hdecomp : x - y = (p - q) + ((x - p) - (y - q)) := by abel
  have hsplit : ⟪x - y, p - q⟫_ℝ
      = ‖p - q‖ ^ 2 + ⟪(x - p) - (y - q), p - q⟫_ℝ := by
    rw [hdecomp, inner_add_left, real_inner_self_eq_norm_sq]
  have hcs : ⟪x - y, p - q⟫_ℝ ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
  by_cases hd : ‖p - q‖ = 0
  · rw [hd]; exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hle : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by
      rw [← pow_two]; linarith
    exact le_of_mul_le_mul_right hle hpos

/-- **Firm nonexpansiveness of nearest-point selection:** the squared
distance between nearest points plus the squared distance between the
residuals is at most the squared distance between the original points. -/
theorem norm_sub_sq_add_norm_sub_sq_le_of_isNearestPoint {K : Set F}
    (hKv : Convex ℝ K) {x y p q : F} (hpK : p ∈ K) (hqK : q ∈ K)
    (hp : ‖x - p‖ = ⨅ w : K, ‖x - w‖)
    (hq : ‖y - q‖ = ⨅ w : K, ‖y - w‖) :
    ‖p - q‖ ^ 2 + ‖(x - p) - (y - q)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hinner := inner_sub_sub_nonneg_of_isNearestPoint hKv hpK hqK hp hq
  have hdecomp : x - y = (p - q) + ((x - p) - (y - q)) := by abel
  have hsq : ‖x - y‖ ^ 2 = ‖p - q‖ ^ 2 + 2 * ⟪p - q, (x - p) - (y - q)⟫_ℝ
      + ‖(x - p) - (y - q)‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real]
  have hcomm : ⟪p - q, (x - p) - (y - q)⟫_ℝ
      = ⟪(x - p) - (y - q), p - q⟫_ℝ := real_inner_comm _ _
  linarith

/-- The projection onto a nonempty complete convex set is `1`-Lipschitz. -/
theorem lipschitzWith_convexProjection {K : Set F} (hKne : K.Nonempty)
    (hKc : IsComplete K) (hKv : Convex ℝ K) :
    LipschitzWith 1 (convexProjection K) := by
  refine lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_
  have h := norm_sub_le_of_isNearestPoint hKv
    (convexProjection_mem hKne hKc hKv x) (convexProjection_mem hKne hKc hKv y)
    (convexProjection_norm_eq_iInf hKne hKc hKv x)
    (convexProjection_norm_eq_iInf hKne hKc hKv y)
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using h

/-- Firm nonexpansiveness of the projection map. -/
theorem convexProjection_firmly_nonexpansive {K : Set F} (hKne : K.Nonempty)
    (hKc : IsComplete K) (hKv : Convex ℝ K) (x y : F) :
    ‖convexProjection K x - convexProjection K y‖ ^ 2 +
        ‖(x - convexProjection K x) - (y - convexProjection K y)‖ ^ 2
      ≤ ‖x - y‖ ^ 2 :=
  norm_sub_sq_add_norm_sub_sq_le_of_isNearestPoint hKv
    (convexProjection_mem hKne hKc hKv x) (convexProjection_mem hKne hKc hKv y)
    (convexProjection_norm_eq_iInf hKne hKc hKv x)
    (convexProjection_norm_eq_iInf hKne hKc hKv y)

end MathlibExt.Analysis.InnerProductSpace.ConvexProjection
