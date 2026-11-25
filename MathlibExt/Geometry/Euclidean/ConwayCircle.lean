/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- **Conway circle theorem.** Let $A$, $B$, $C$ be affinely independent points of the Euclidean
plane, and write $a = d(B, C)$, $b = d(A, C)$, $c = d(A, B)$ for the side lengths, where $d$ is
the Euclidean distance. Extend each side beyond each of its endpoints by the length of the side
opposite that endpoint; this gives the six points

$$A + \tfrac{a}{c}(A - B),\quad B + \tfrac{b}{c}(B - A),\quad B + \tfrac{b}{a}(B - C),$$

$$C + \tfrac{c}{a}(C - B),\quad C + \tfrac{c}{b}(C - A),\quad A + \tfrac{a}{b}(A - C).$$

Then there are a point $O$ and a real number $r$ such that all six points are at distance $r$
from $O$.

Proves `Wanted` entry `conway_circle_theorem` (statement `conway-circle-s1`).

Source: https://en.wikipedia.org/wiki/Conway_circle_theorem
-/
theorem conway_circle_theorem (A B C : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ (![A, B, C] : Fin 3 → EuclideanSpace ℝ (Fin 2))) :
    ∃ (O : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
      A + (dist B C / dist A B) • (A - B) ∈ Metric.sphere O r ∧
      B + (dist A C / dist A B) • (B - A) ∈ Metric.sphere O r ∧
      B + (dist A C / dist B C) • (B - C) ∈ Metric.sphere O r ∧
      C + (dist A B / dist B C) • (C - B) ∈ Metric.sphere O r ∧
      C + (dist A B / dist A C) • (C - A) ∈ Metric.sphere O r ∧
      A + (dist B C / dist A C) • (A - C) ∈ Metric.sphere O r := by
  -- The triangle is nondegenerate, so vertices are pairwise distinct.
  have hinj := hABC.injective
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hAB : A ≠ B := fun h => h01 (hinj (by simpa using h))
  have hAC : A ≠ C := fun h => h02 (hinj (by simpa using h))
  have hBC : B ≠ C := fun h => h12 (hinj (by simpa using h))
  -- Side lengths: a opposite A, b opposite B, c opposite C.
  set a := dist B C with ha
  set b := dist A C with hb
  set c := dist A B with hc
  have ha0 : 0 < a := by rw [ha]; exact dist_pos.mpr hBC
  have hb0 : 0 < b := by rw [hb]; exact dist_pos.mpr hAC
  have hc0 : 0 < c := by rw [hc]; exact dist_pos.mpr hAB
  have ha0' : a ≠ 0 := ne_of_gt ha0
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have hc0' : c ≠ 0 := ne_of_gt hc0
  set p := a + b + c with hp
  have hp0 : 0 < p := by rw [hp]; exact add_pos (add_pos ha0 hb0) hc0
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have habc : a + b + c ≠ 0 := ne_of_gt (add_pos (add_pos ha0 hb0) hc0)
  -- The center is the incenter, as a barycentric combination.
  set O : EuclideanSpace ℝ (Fin 2) := p⁻¹ • (a • A + b • B + c • C) with hO
  -- Norms of the edge vectors.
  have e1n : ‖B - A‖ = c := by rw [hc, ← dist_eq_norm]; exact dist_comm _ _
  have e2n : ‖C - A‖ = b := by rw [hb, ← dist_eq_norm]; exact dist_comm _ _
  have haN : ‖B - C‖ = a := by rw [ha, ← dist_eq_norm]
  have h11 : ‖B - A‖ ^ 2 = c ^ 2 := by rw [e1n]
  have h22 : ‖C - A‖ ^ 2 = b ^ 2 := by rw [e2n]
  -- Inner product of the edge vectors (law of cosines).
  set g := inner ℝ (B - A) (C - A) with hgdef
  have hcomm2 : inner ℝ (C - A) (B - A) = g := by
    rw [hgdef]; exact real_inner_comm _ _
  have hg : g = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by
    have h := norm_sub_sq_real (B - A) (C - A)
    have he : (B - A) - (C - A) = B - C := by abel
    rw [he, haN, e1n, e2n, ← hgdef] at h
    linarith
  -- Squared norm of a combination of the edge vectors.
  have key : ∀ α β : ℝ, ‖α • (B - A) + β • (C - A)‖ ^ 2
      = α ^ 2 * c ^ 2 + 2 * α * β * g + β ^ 2 * b ^ 2 := by
    intro α β
    conv_lhs => rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq, h11, h22, ← hgdef, hcomm2]
    ring
  -- Clearing the center's denominator, per multiplier.
  have tOc : (p * c) * p⁻¹ = c := by field_simp
  have tOa : (p * a) * p⁻¹ = a := by field_simp
  have tOb : (p * b) * p⁻¹ = b := by field_simp
  have eOc : (p * c) • O = c • (a • A + b • B + c • C) := by
    rw [hO, smul_smul, tOc]
  have eOa : (p * a) • O = a • (a • A + b • B + c • C) := by
    rw [hO, smul_smul, tOa]
  have eOb : (p * b) • O = b • (a • A + b • B + c • C) := by
    rw [hO, smul_smul, tOb]
  have hpc : p * c ≠ 0 := mul_ne_zero hp0' hc0'
  have hpa : p * a ≠ 0 := mul_ne_zero hp0' ha0'
  have hpb : p * b ≠ 0 := mul_ne_zero hp0' hb0'
  -- First extension point beyond A along AB.
  have tP_A1 : (p * c) * (a / c) = p * a := by field_simp
  have sA_A1 : (p * c) * (-(a / c) - b * p⁻¹) = -(p * a) - b * c := by field_simp
  have sB_A1 : (p * c) * (-(c * p⁻¹)) = -(c * c) := by field_simp
  have eA1 : (A + (a / c) • (A - B)) - O
      = (-(a / c) - b * p⁻¹) • (B - A) + (-(c * p⁻¹)) • (C - A) := by
    have h1 : (p * c) • ((A + (a / c) • (A - B)) - O)
        = (p * c) • ((-(a / c) - b * p⁻¹) • (B - A)
          + (-(c * p⁻¹)) • (C - A)) := by
      simp only [smul_sub, smul_add, smul_smul, eOc, tP_A1, sA_A1, sB_A1]
      rw [hp]
      module
    exact smul_right_injective _ hpc h1
  -- Second extension point: beyond B along BA.
  have tP_B1 : (p * c) * (b / c) = p * b := by field_simp
  have sA_B1 : (p * c) * (1 + (b / c) - b * p⁻¹)
      = (p * c) + (p * b) - b * c := by field_simp
  have eB1 : (B + (b / c) • (B - A)) - O
      = (1 + (b / c) - b * p⁻¹) • (B - A) + (-(c * p⁻¹)) • (C - A) := by
    have h1 : (p * c) • ((B + (b / c) • (B - A)) - O)
        = (p * c) • ((1 + (b / c) - b * p⁻¹) • (B - A)
          + (-(c * p⁻¹)) • (C - A)) := by
      simp only [smul_sub, smul_add, smul_smul, eOc, tP_B1, sA_B1, sB_A1]
      rw [hp]
      module
    exact smul_right_injective _ hpc h1
  -- Third extension point: beyond B along BC.
  have tP_B2 : (p * a) * (b / a) = p * b := by field_simp
  have sA_B2 : (p * a) * (1 + (b / a) - b * p⁻¹)
      = (p * a) + (p * b) - b * a := by field_simp
  have sB_B2 : (p * a) * (-(b / a) - c * p⁻¹) = -(p * b) - c * a := by field_simp
  have eB2 : (B + (b / a) • (B - C)) - O
      = (1 + (b / a) - b * p⁻¹) • (B - A)
        + (-(b / a) - c * p⁻¹) • (C - A) := by
    have h1 : (p * a) • ((B + (b / a) • (B - C)) - O)
        = (p * a) • ((1 + (b / a) - b * p⁻¹) • (B - A)
          + (-(b / a) - c * p⁻¹) • (C - A)) := by
      simp only [smul_sub, smul_add, smul_smul, eOa, tP_B2, sA_B2, sB_B2]
      rw [hp]
      module
    exact smul_right_injective _ hpa h1
  -- Fourth extension point: beyond C along CB.
  have tP_C1 : (p * a) * (c / a) = p * c := by field_simp
  have sA_C1 : (p * a) * (-(c / a) - b * p⁻¹) = -(p * c) - b * a := by field_simp
  have sB_C1 : (p * a) * ((c / a) + 1 - c * p⁻¹)
      = (p * c) + (p * a) - c * a := by field_simp
  have eC1 : (C + (c / a) • (C - B)) - O
      = (-(c / a) - b * p⁻¹) • (B - A)
        + ((c / a) + 1 - c * p⁻¹) • (C - A) := by
    have h1 : (p * a) • ((C + (c / a) • (C - B)) - O)
        = (p * a) • ((-(c / a) - b * p⁻¹) • (B - A)
          + ((c / a) + 1 - c * p⁻¹) • (C - A)) := by
      simp only [smul_sub, smul_add, smul_smul, eOa, tP_C1, sA_C1, sB_C1]
      rw [hp]
      module
    exact smul_right_injective _ hpa h1
  -- Fifth extension point: beyond C along CA.
  have tP_C2 : (p * b) * (c / b) = p * c := by field_simp
  have sA_C2 : (p * b) * (-(b * p⁻¹)) = -(b * b) := by field_simp
  have sB_C2 : (p * b) * ((c / b) + 1 - c * p⁻¹)
      = (p * c) + (p * b) - c * b := by field_simp
  have eC2 : (C + (c / b) • (C - A)) - O
      = (-(b * p⁻¹)) • (B - A) + ((c / b) + 1 - c * p⁻¹) • (C - A) := by
    have h1 : (p * b) • ((C + (c / b) • (C - A)) - O)
        = (p * b) • ((-(b * p⁻¹)) • (B - A)
          + ((c / b) + 1 - c * p⁻¹) • (C - A)) := by
      simp only [smul_sub, smul_add, smul_smul, eOb, tP_C2, sA_C2, sB_C2]
      rw [hp]
      module
    exact smul_right_injective _ hpb h1
  -- Sixth extension point: beyond A along AC.
  have tP_A2 : (p * b) * (a / b) = p * a := by field_simp
  have sB_A2 : (p * b) * (-(a / b) - c * p⁻¹) = -(p * a) - c * b := by field_simp
  have eA2 : (A + (a / b) • (A - C)) - O
      = (-(b * p⁻¹)) • (B - A) + (-(a / b) - c * p⁻¹) • (C - A) := by
    have h1 : (p * b) • ((A + (a / b) • (A - C)) - O)
        = (p * b) • ((-(b * p⁻¹)) • (B - A)
          + (-(a / b) - c * p⁻¹) • (C - A)) := by
      simp only [smul_sub, smul_add, smul_smul, eOb, tP_A2, sA_C2, sB_A2]
      rw [hp]
      module
    exact smul_right_injective _ hpb h1
  -- All six points share the first point's distance from O.
  refine ⟨O, dist (A + (a / c) • (A - B)) O, Metric.mem_sphere.mpr rfl, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [Metric.mem_sphere, dist_eq_norm, dist_eq_norm]
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [eB1, eA1, key, key, hg, hp]
    field_simp
    ring
  · rw [Metric.mem_sphere, dist_eq_norm, dist_eq_norm]
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [eB2, eA1, key, key, hg, hp]
    field_simp
    ring
  · rw [Metric.mem_sphere, dist_eq_norm, dist_eq_norm]
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [eC1, eA1, key, key, hg, hp]
    field_simp
    ring
  · rw [Metric.mem_sphere, dist_eq_norm, dist_eq_norm]
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [eC2, eA1, key, key, hg, hp]
    field_simp
    ring
  · rw [Metric.mem_sphere, dist_eq_norm, dist_eq_norm]
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [eA2, eA1, key, key, hg, hp]
    field_simp
    ring

end MetaMathlibExt
