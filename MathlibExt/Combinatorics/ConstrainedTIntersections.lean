/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Four-point intersections of constrained T's

Two constrained long-legged T's with four distinct intersection points have stem directions
with negative cosine.
-/

namespace MetaMathlibExt

namespace cos_sub_neg_of_tbar_inter_ncard_four

private noncomputable def crossbar (c : ℝ × ℝ) (θ : ℝ) : Set (ℝ × ℝ) :=
  Set.range fun s : ℝ => c + s • (-Real.sin θ, Real.cos θ)

private noncomputable def stemPoint (c : ℝ × ℝ) (θ s : ℝ) : ℝ × ℝ :=
  c + s • (Real.cos θ, Real.sin θ)

private noncomputable def stem (c : ℝ × ℝ) (θ : ℝ) : Set (ℝ × ℝ) :=
  stemPoint c θ '' Set.Ici 0

private theorem convex_image {s : Set ℝ} (hs : Convex ℝ s) (c v : ℝ × ℝ) :
    Convex ℝ ((fun t : ℝ => c + t • v) '' s) := by
  have hmap : (AffineMap.lineMap c (c + v) : ℝ → ℝ × ℝ) = fun t => c + t • v := by
    funext t
    simp [AffineMap.lineMap_apply_module', add_comm]
  simpa only [hmap] using hs.affine_image (AffineMap.lineMap c (c + v))

private theorem crossbar_convex (c : ℝ × ℝ) (θ : ℝ) : Convex ℝ (crossbar c θ) := by
  rw [crossbar, ← Set.image_univ]
  exact convex_image convex_univ _ _

private theorem stem_convex (c : ℝ × ℝ) (θ : ℝ) : Convex ℝ (stem c θ) :=
  convex_image (convex_Ici 0) _ _

private theorem center_mem_crossbar (c : ℝ × ℝ) (θ : ℝ) : c ∈ crossbar c θ :=
  ⟨0, by simp⟩

private noncomputable def projection (c : ℝ × ℝ) (θ : ℝ) (x : ℝ × ℝ) : ℝ :=
  (x.1 - c.1) * Real.cos θ + (x.2 - c.2) * Real.sin θ

private theorem projection_crossbar {c x : ℝ × ℝ} {θ : ℝ} (hx : x ∈ crossbar c θ) :
    projection c θ x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  simp [projection]
  ring

private theorem projection_stemPoint (c d : ℝ × ℝ) (θ φ s : ℝ) :
    projection c θ (stemPoint d φ s) = projection c θ d + s * Real.cos (θ - φ) := by
  simp [projection, stemPoint, Real.cos_sub]
  ring

/-- Project the common stem point and the mixed crossing onto the first stem direction. -/
private theorem stem_parameter {c d : ℝ × ℝ} {θ φ s t a : ℝ}
    (hcross : stemPoint d φ a ∈ crossbar c θ)
    (hpoint : stemPoint c θ s = stemPoint d φ t) :
    s = (t - a) * Real.cos (θ - φ) := by
  have hzero := projection_crossbar hcross
  rw [projection_stemPoint] at hzero
  have h := congrArg (projection c θ) hpoint
  rw [projection_stemPoint, projection_stemPoint, sub_self, Real.cos_zero, mul_one] at h
  have hc : projection c θ c = 0 := by simp [projection]
  rw [hc, zero_add] at h
  linarith

end cos_sub_neg_of_tbar_inter_ncard_four

open cos_sub_neg_of_tbar_inter_ncard_four in
/-- **Four-point intersections of constrained T's.** For a point $c \in \mathbb{R}^2$ and an angle
$\theta \in \mathbb{R}$, the constrained long-legged T $\bar T(c, \theta)$ is the union of the
crossbar, the line $\{c + s(-\sin\theta, \cos\theta) : s \in \mathbb{R}\}$, and the stem, the ray
$\{c + s(\cos\theta, \sin\theta) : s \ge 0\}$. For all $c_1, c_2 \in \mathbb{R}^2$ and
$\theta_1, \theta_2 \in \mathbb{R}$, if $\bar T(c_1, \theta_1) \cap \bar T(c_2, \theta_2)$ has
exactly four points, then $\cos(\theta_1 - \theta_2) < 0$, that is, the two stem directions make
an angle greater than $\pi/2$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Lemma 2
(`jis-2026-26.4.5-lem-2`), with the definition in the subsection *The constrained long-legged T̄*.
-/
public theorem cos_sub_neg_of_tbar_inter_ncard_four (c₁ c₂ : ℝ × ℝ) (θ₁ θ₂ : ℝ) :
    let T : ℝ × ℝ → ℝ → Set (ℝ × ℝ) := fun c θ =>
      Set.range (fun s : ℝ => c + s • (-Real.sin θ, Real.cos θ)) ∪
        (fun s : ℝ => c + s • (Real.cos θ, Real.sin θ)) '' Set.Ici 0
    (T c₁ θ₁ ∩ T c₂ θ₂).ncard = 4 → Real.cos (θ₁ - θ₂) < 0 := by
  change ((crossbar c₁ θ₁ ∪ stem c₁ θ₁) ∩ (crossbar c₂ θ₂ ∪ stem c₂ θ₂)).ncard = 4 → _
  intro hcard
  by_contra! hcos
  let bars := crossbar c₁ θ₁ ∩ crossbar c₂ θ₂
  let stemBar := stem c₁ θ₁ ∩ crossbar c₂ θ₂
  let barStem := crossbar c₁ θ₁ ∩ stem c₂ θ₂
  let stems := stem c₁ θ₁ ∩ stem c₂ θ₂
  rw [Set.inter_union_distrib_left, Set.union_inter_distrib_right,
    Set.union_inter_distrib_right] at hcard
  change ((bars ∪ stemBar) ∪ (barStem ∪ stems)).ncard = 4 at hcard
  have hfinite := Set.finite_of_ncard_ne_zero (hcard.trans_ne (by decide))
  obtain ⟨hleftFinite, hrightFinite⟩ := Set.finite_union.mp hfinite
  obtain ⟨hbars, hstemBar⟩ := Set.finite_union.mp hleftFinite
  obtain ⟨hbarStem, hstems⟩ := Set.finite_union.mp hrightFinite
  -- A finite convex intersection has at most one point.
  have limit {s : Set (ℝ × ℝ)} (hf : s.Finite) (hc : Convex ℝ s) : s.ncard ≤ 1 :=
    (Set.ncard_le_one hf).mpr (hc.isPreconnected.isDiscrete_iff_subsingleton.mp hf.isDiscrete)
  have hbars₁ := limit hbars ((crossbar_convex c₁ θ₁).inter (crossbar_convex c₂ θ₂))
  have hstemBar₁ := limit hstemBar ((stem_convex c₁ θ₁).inter (crossbar_convex c₂ θ₂))
  have hbarStem₁ := limit hbarStem ((crossbar_convex c₁ θ₁).inter (stem_convex c₂ θ₂))
  have hstems₁ := limit hstems ((stem_convex c₁ θ₁).inter (stem_convex c₂ θ₂))
  have hleft := Set.ncard_union_le bars stemBar
  have hright := Set.ncard_union_le barStem stems
  have htotal := Set.ncard_union_le (bars ∪ stemBar) (barStem ∪ stems)
  -- Four points require equality in both union bounds, so the summands are disjoint.
  have hleftDisj := (Set.ncard_union_eq_iff hbars hstemBar).mp (by omega)
  have hrightDisj := (Set.ncard_union_eq_iff hbarStem hstems).mp (by omega)
  obtain ⟨_, ⟨⟨a, ha, rfl⟩, haBar⟩⟩ :=
    Set.nonempty_of_ncard_ne_zero (s := stemBar) (by omega)
  obtain ⟨_, ⟨hbBar, ⟨b, hb, rfl⟩⟩⟩ :=
    Set.nonempty_of_ncard_ne_zero (s := barStem) (by omega)
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := stems) (by omega)
  obtain ⟨s, hs, hsx⟩ := hx.1
  obtain ⟨t, ht, htx⟩ := hx.2
  have hsparam := stem_parameter hbBar (hsx.trans htx.symm)
  have htparam := stem_parameter haBar (htx.trans hsx.symm)
  rw [← neg_sub θ₁ θ₂, Real.cos_neg] at htparam
  have hsle : s ≤ t := by
    have hbcos := mul_nonneg hb hcos
    have htcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (θ₁ - θ₂)) ht
    linarith
  have hazero : a * Real.cos (θ₁ - θ₂) = 0 := by
    have hacos := mul_nonneg ha hcos
    have hscos := mul_le_mul_of_nonneg_left (Real.cos_le_one (θ₁ - θ₂)) hs
    linarith
  rcases mul_eq_zero.mp hazero with ha₀ | hcos₀
  · have hp : stemPoint c₁ θ₁ a ∈ crossbar c₁ θ₁ := by
      simpa [ha₀, stemPoint] using center_mem_crossbar c₁ θ₁
    exact Set.disjoint_left.mp hleftDisj ⟨hp, haBar⟩ ⟨⟨a, ha, rfl⟩, haBar⟩
  · have hs₀ : s = 0 := by simpa [hcos₀] using hsparam
    have hxBar : x ∈ crossbar c₁ θ₁ := by
      rw [← hsx]
      simpa [hs₀, stemPoint] using center_mem_crossbar c₁ θ₁
    exact Set.disjoint_left.mp hrightDisj ⟨hxBar, hx.2⟩ hx

end MetaMathlibExt
