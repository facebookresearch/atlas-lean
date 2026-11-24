/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Radon line agreement

For an orthonormal pair in the Euclidean plane, the hyperplane at signed distance p is exactly the parametrized line through p times the normal in the direction of the tangent vector; reversing the tangent orientation does not change the line. This is the set-level agreement underlying the Euclidean Radon transform on lines.
-/

@[expose] public section

open InnerProductSpace

namespace MathlibExt.Analysis.IntegralGeometry.RadonLineAgreement

/-- **The hyperplane is the parametrized line.** For unit vectors
`xi, eta` in the Euclidean plane with `⟪xi, eta⟫ = 0`, the line
`{x | ⟪x, xi⟫_R = p}` is exactly the range of the parametrization
`s ↦ p • xi + s • eta`. -/
theorem line_set_eq_range {xi eta : EuclideanSpace ℝ (Fin 2)}
    (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) (hortho : @inner ℝ _ _ xi eta = 0) (p : ℝ) :
    {x : EuclideanSpace ℝ (Fin 2) | @inner ℝ _ _ x xi = p} =
      Set.range (fun s : ℝ => p • xi + s • eta) := by
  have hcomm : @inner ℝ _ _ eta xi = 0 := by
    rw [real_inner_comm]; exact hortho
  have hon : Orthonormal ℝ ![xi, eta] := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i
      · simpa using hxi
      · simpa using heta
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa using hortho
      · simpa using hcomm
      · exact absurd rfl hij
  have hli : LinearIndependent ℝ ![xi, eta] := hon.linearIndependent
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [finrank_euclideanSpace]
  have hsp : Submodule.span ℝ (Set.range ![xi, eta]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  set b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    OrthonormalBasis.mk hon hsp.ge with hb
  have hb0 : b 0 = xi := by simp [hb]
  have hb1 : b 1 = eta := by simp [hb]
  ext x
  constructor
  · intro hx
    simp only [Set.mem_ofPred_eq] at hx
    refine ⟨@inner ℝ _ _ x eta, ?_⟩
    have hdecomp := b.sum_repr' x
    rw [Fin.sum_univ_two] at hdecomp
    rw [hb0, hb1] at hdecomp
    have h0 : @inner ℝ _ _ xi x = p := by rw [real_inner_comm]; exact hx
    have h1 : @inner ℝ _ _ eta x = @inner ℝ _ _ x eta := real_inner_comm _ _
    rw [h0, h1] at hdecomp
    exact hdecomp
  · rintro ⟨s, rfl⟩
    show @inner ℝ _ _ (p • xi + s • eta) xi = p
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hxx : @inner ℝ _ _ xi xi = 1 := by
      rw [real_inner_self_eq_norm_sq, hxi, one_pow]
    rw [hxx, hcomm, mul_one, mul_zero, add_zero]

/-- **Orientation invariance.** Reversing the direction `eta`
parametrizes the same line: the ranges for `eta` and `-eta`
agree. -/
theorem line_range_neg {xi eta : EuclideanSpace ℝ (Fin 2)} (p : ℝ) :
    Set.range (fun s : ℝ => p • xi + s • eta) =
      Set.range (fun s : ℝ => p • xi + s • (-eta)) := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨-s, by simp [smul_neg, neg_smul]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨-s, by simp [smul_neg, neg_smul]⟩


end MathlibExt.Analysis.IntegralGeometry.RadonLineAgreement
