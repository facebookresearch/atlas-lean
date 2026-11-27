/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import MathlibExt.Topology.MetricSpace.GeodesicSpace
public import MathlibExt.Topology.MetricSpace.GromovHyperbolic

/-!
# Basic properties of Gromov-hyperbolic spaces

This file proves the first properties of `δ`-hyperbolic spaces (`Metric.IsDeltaHyperbolic`) from
Gromov, *Hyperbolic groups*, Essays in Group Theory, MSRI Publ. 8, Springer (1987), 75-263.

* Base-point change (§1.1.A, 1.1.B): if the `δ`-inequality holds with respect to one base point,
  then the four-point inequality holds with constant `2δ`, and the space is `2δ`-hyperbolic.
* First examples (§1.2): the real line is `0`-hyperbolic, a space of diameter at most `d` is
  `d`-hyperbolic, and hyperbolicity passes to subspaces (isometric embeddings), so `ℤ` is
  `0`-hyperbolic.
* Thin triangles (§6.3): in Gromov's tripod sense, geodesic triangles in a `δ`-hyperbolic space
  are `4δ`-thin, and a geodesic space whose triangles are `δ`-thin is `δ`-hyperbolic. Gromov's
  Proposition 6.3.C has the constants `2δ` and `2δ`: our first constant is weaker (Gromov's `2δ`
  uses approximating trees, §6.1, which are not formalised), our second one is stronger (the
  lower bound (**) in Gromov's proof of 6.3.B holds without the `-δ`, by the triangle inequality).

## Main definitions

* `Metric.TrianglesThin X δ`: every geodesic triangle in `X` is `δ`-thin in Gromov's sense
  (§6.3): points on two sides issuing from a common vertex `x`, at the same distance
  `t ≤ (y ∣ z)_x` from `x`, are at most `δ` apart.

## Main results

* `Metric.four_point_of_basepoint`, `Metric.isDeltaHyperbolic_two_mul_of_basepoint`: §1.1.A-B.
* `Metric.isDeltaHyperbolic_real`: §1.2(a).
* `Metric.isDeltaHyperbolic_of_forall_dist_le`: §1.2(b).
* `Metric.IsDeltaHyperbolic.of_isometry`, `Metric.isDeltaHyperbolic_int`.
* `Metric.IsDeltaHyperbolic.trianglesThin`, `Metric.isDeltaHyperbolic_of_trianglesThin`: §6.3.
-/

@[expose] public section

namespace Metric

open Set

variable {X : Type*} [PseudoMetricSpace X]

/-! ### Change of base point -/

/-- **The four-point inequality from one base point** (Gromov, *Hyperbolic groups*, 1987,
Lemma 1.1.A). If `(x ∣ y)_o ≥ min ((x ∣ z)_o, (y ∣ z)_o) - δ` for all `x y z` and one fixed base
point `o`, then for all `x y z t`,
`(t ∣ y)_o + (z ∣ x)_o ≥ min ((t ∣ z)_o + (y ∣ x)_o, (x ∣ t)_o + (y ∣ z)_o) - 2δ`. -/
theorem four_point_of_basepoint {o : X} {δ : ℝ}
    (h : ∀ x y z : X, min (gromovProduct o x y) (gromovProduct o y z) - δ ≤ gromovProduct o x z)
    (x y z t : X) :
    min (gromovProduct o t z + gromovProduct o y x) (gromovProduct o x t + gromovProduct o y z)
      - 2 * δ ≤ gromovProduct o t y + gromovProduct o z x := by
  have h1 := h t z y
  have h2 := h t x y
  have h3 := h z t x
  have h4 := h z y x
  rw [gromovProduct_comm o z y] at h1
  rw [gromovProduct_comm o t x] at h2 h3
  rw [gromovProduct_comm o x y] at h2
  rw [gromovProduct_comm o z t] at h3
  rw [gromovProduct_comm o z y] at h4
  generalize gromovProduct o t z = a at *
  generalize gromovProduct o y x = b at *
  generalize gromovProduct o x t = c at *
  generalize gromovProduct o y z = d at *
  generalize gromovProduct o t y = P at *
  generalize gromovProduct o z x = Q at *
  simp only [min_def] at *
  split_ifs at * <;> linarith

/-- **Hyperbolicity with respect to one base point gives hyperbolicity** (Gromov, *Hyperbolic
groups*, 1987, Corollary 1.1.B). If `X` is `δ`-hyperbolic with respect to one base point `o`
(the `δ`-inequality (*) of §1.1 holds for all `x y z` with base point `o`) and `0 ≤ δ`, then `X`
is `2δ`-hyperbolic (with respect to every base point, Definition 1.1.C). -/
theorem isDeltaHyperbolic_two_mul_of_basepoint {o : X} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x y z : X, min (gromovProduct o x y) (gromovProduct o y z) - δ ≤ gromovProduct o x z) :
    IsDeltaHyperbolic X (2 * δ) := by
  refine ⟨by linarith, fun w x y z => ?_⟩
  have key := four_point_of_basepoint h w z y x
  simp only [gromovProduct_eq] at key ⊢
  simp only [dist_comm] at key ⊢
  simp only [min_def] at key ⊢
  split_ifs at key ⊢ <;> linarith

/-! ### First examples -/

/-- **Bounded spaces are hyperbolic** (Gromov, *Hyperbolic groups*, 1987, §1.2(b)). If all
distances in `X` are at most `d` and `0 ≤ d`, then `X` is `d`-hyperbolic. -/
theorem isDeltaHyperbolic_of_forall_dist_le {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ x y : X, dist x y ≤ d) : IsDeltaHyperbolic X d := by
  refine ⟨hd, fun w x y z => ?_⟩
  have h1 := min_le_left (gromovProduct w x y) (gromovProduct w y z)
  have h2 := gromovProduct_le_dist_left w x y
  have h3 := gromovProduct_nonneg w x z
  have h4 := h w x
  linarith

/-- **Hyperbolicity passes to subspaces.** If `f : Y → X` is an isometric embedding and `X` is
`δ`-hyperbolic, then `Y` is `δ`-hyperbolic. -/
theorem IsDeltaHyperbolic.of_isometry {Y : Type*} [PseudoMetricSpace Y] {f : Y → X}
    (hf : Isometry f) {δ : ℝ} (h : IsDeltaHyperbolic X δ) : IsDeltaHyperbolic Y δ := by
  refine ⟨h.1, fun w x y z => ?_⟩
  have := h.four_point (f w) (f x) (f y) (f z)
  simpa only [gromovProduct_eq, hf.dist_eq] using this

/-- **The real line is `0`-hyperbolic** (Gromov, *Hyperbolic groups*, 1987, §1.2(a)). -/
theorem isDeltaHyperbolic_real : IsDeltaHyperbolic ℝ 0 := by
  refine ⟨le_rfl, fun w x y z => ?_⟩
  simp only [gromovProduct_eq, Real.dist_eq, sub_zero]
  rcases abs_cases (w - x) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases abs_cases (w - y) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  rcases abs_cases (w - z) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
  rcases abs_cases (x - y) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
  rcases abs_cases (y - z) with ⟨h5, _⟩ | ⟨h5, _⟩ <;>
  rcases abs_cases (x - z) with ⟨h6, _⟩ | ⟨h6, _⟩ <;>
  rw [h1, h2, h3, h4, h5, h6, min_def] <;>
  split_ifs <;> linarith

/-- **The integers are `0`-hyperbolic.** `ℤ` with its usual metric (the simplicial line, a tree)
is `0`-hyperbolic, as a subspace of the real line. -/
theorem isDeltaHyperbolic_int : IsDeltaHyperbolic ℤ 0 :=
  isDeltaHyperbolic_real.of_isometry (Isometry.of_dist_eq Int.dist_cast_real)

/-! ### Thin triangles -/

/-- **Thin geodesic triangles.** Every geodesic triangle in `X` is `δ`-thin in Gromov's tripod
sense (*Hyperbolic groups*, 1987, §6.3): for every vertex `x`, all geodesic segments `γ` from `x`
to `y` and `γ'` from `x` to `z`, and every `t` with `0 ≤ t ≤ (y ∣ z)_x`, the points `γ t` and
`γ' t` (which have the same image in the comparison tripod) satisfy `d(γ t, γ' t) ≤ δ`. -/
def TrianglesThin (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  ∀ (x y z : X) (γ γ' : ℝ → X), IsGeodesicSegment γ x y → IsGeodesicSegment γ' x z →
    ∀ t : ℝ, 0 ≤ t → t ≤ gromovProduct x y z → dist (γ t) (γ' t) ≤ δ

/-- **Geodesic triangles in a hyperbolic space are thin** (compare Gromov, *Hyperbolic groups*,
1987, Lemma 6.3.A and Proposition 6.3.C, which give the sharper constant `2δ`). If `X` is
`δ`-hyperbolic, every geodesic triangle in `X` is `4δ`-thin. -/
theorem IsDeltaHyperbolic.trianglesThin {δ : ℝ} (h : IsDeltaHyperbolic X δ) :
    TrianglesThin X (4 * δ) := by
  intro x y z γ γ' hγ hγ' t ht₀ ht
  have hty : t ≤ dist x y := ht.trans (gromovProduct_le_dist_left x y z)
  have htz : t ≤ dist x z := ht.trans (gromovProduct_le_dist_right x y z)
  have hu1 := hγ.dist_left ht₀ hty
  have hu2 := hγ.dist_right ht₀ hty
  have hv1 := hγ'.dist_left ht₀ htz
  have hv2 := hγ'.dist_right ht₀ htz
  -- `(γ t ∣ y)_x = t` and `(z ∣ γ' t)_x = t`
  have e1 : gromovProduct x (γ t) y = t := by
    rw [gromovProduct_eq, hu1, hu2]; ring
  have e2 : gromovProduct x z (γ' t) = t := by
    rw [gromovProduct_eq, hv1, dist_comm z (γ' t), hv2]; ring
  have k1 := h.four_point x (γ t) y (γ' t)
  have k2 := h.four_point x y z (γ' t)
  rw [e1] at k1
  rw [e2] at k2
  have k3 : t - δ ≤ gromovProduct x y (γ' t) := by
    rcases le_total (gromovProduct x y z) t with a | a
    · have : gromovProduct x y z = t := le_antisymm a ht
      rw [this, min_self] at k2; exact k2
    · rw [min_eq_right a] at k2; exact k2
  have hδ := h.nonneg
  have k4 : t - 2 * δ ≤ gromovProduct x (γ t) (γ' t) := by
    rcases le_total t (gromovProduct x y (γ' t)) with a | a
    · rw [min_eq_left a] at k1; linarith
    · rw [min_eq_right a] at k1; linarith
  rw [gromovProduct_eq, hu1, hv1] at k4
  linarith

/-- **Thin triangles imply hyperbolicity** (compare Gromov, *Hyperbolic groups*, 1987,
Lemma 6.3.B and Proposition 6.3.C, which give the weaker conclusion `2δ`). If `X` is a geodesic
space whose geodesic triangles are all `δ`-thin and `0 ≤ δ`, then `X` is `δ`-hyperbolic. -/
theorem isDeltaHyperbolic_of_trianglesThin {δ : ℝ} (hδ : 0 ≤ δ) (hX : IsGeodesicSpace X)
    (h : TrianglesThin X δ) : IsDeltaHyperbolic X δ := by
  refine ⟨hδ, fun w x y z => ?_⟩
  obtain ⟨γx, hx⟩ := hX w x
  obtain ⟨γy, hy⟩ := hX w y
  obtain ⟨γz, hz⟩ := hX w z
  set t := min (gromovProduct w x y) (gromovProduct w y z) with ht
  have ht₀ : 0 ≤ t := le_min (gromovProduct_nonneg _ _ _) (gromovProduct_nonneg _ _ _)
  have htxy : t ≤ gromovProduct w x y := min_le_left _ _
  have htyz : t ≤ gromovProduct w y z := min_le_right _ _
  have htx : t ≤ dist w x := htxy.trans (gromovProduct_le_dist_left _ _ _)
  have htz : t ≤ dist w z := htyz.trans (gromovProduct_le_dist_right _ _ _)
  have d1 := h w x y γx γy hx hy t ht₀ htxy
  have d2 := h w y z γy γz hy hz t ht₀ htyz
  have d3 := hx.dist_right ht₀ htx
  have d4 := hz.dist_right ht₀ htz
  have tri : dist x z ≤ dist x (γx t) + dist (γx t) (γy t) + dist (γy t) (γz t) +
      dist (γz t) z := by
    have := dist_triangle4 x (γx t) (γz t) z
    have := dist_triangle (γx t) (γy t) (γz t)
    linarith
  rw [dist_comm x (γx t)] at tri
  rw [gromovProduct_eq]
  linarith

end Metric
