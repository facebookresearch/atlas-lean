/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.FiniteAbelianDFT
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Tactic

/-!
# Uncertainty principle on a finite abelian group

A function on a finite abelian group and its discrete Fourier transform
cannot both be concentrated on small sets. This is the Donoho–Stark
uncertainty principle: if `f : G → ℂ` is nonzero, then

  `|G| ≤ |supp f| * |supp f̂|`.

The proof is the classical one. Fourier inversion writes each value
`f x` as an average over the Fourier support, Cauchy–Schwarz bounds that
average by the `ℓ²` mass of `f̂`, and Plancherel identifies the `ℓ²` mass
of `f̂` with `|G|` times the `ℓ²` mass of `f`. We prove the principle in
the stronger "concentration" form: if `f̂` vanishes outside `B`, then the
`ℓ²` mass of `f` on any set `A` is at most `(|A| * |B| / |G|)` times the
total `ℓ²` mass of `f` (and dually, with the roles of `f` and `f̂`
exchanged). The Donoho–Stark bound and the nonvanishing corollary follow by
taking `A` and `B` to be the supports.

This is a companion to the Fourier material of
`v1/Atlas/IntroductionToFunctionalAnalysis` (the Fejér theorem, Fourier
series, the Riemann–Lebesgue lemma) and to the discrete Fourier transform
`dftFun` in `MathlibExt/Analysis/Fourier/FiniteAbelianDFT.lean`. It is not
one of the 72 v1 targets. The finite-group uncertainty principle is not in
the pinned Mathlib (which has character orthogonality and Pontryagin
duality, but no support-product bound) or in base MathlibExt.

Sources: D. Donoho and P. Stark, "Uncertainty principles and signal
recovery", *SIAM Journal on Applied Mathematics* 49 (1989), 906–931;
T. Tao, "An uncertainty principle for cyclic groups of prime order",
*Mathematical Research Letters* 12 (2005), 121–127 (for the prime-order
refinement, which is not proved here).

## Main declarations

* `sum_norm_sq_dftFun` : Plancherel in squared-norm form.
* `norm_sq_le_of_dftFun_eq_zero_of_notMem` : pointwise bound for `f x`
  in terms of the size of a set containing the Fourier support.
* `sum_norm_sq_le_of_dftFun_eq_zero_of_notMem` : concentration of `f`
  on `A` when `f̂` vanishes outside `B`.
* `sum_norm_sq_dftFun_le_of_eq_zero_of_notMem` : the dual concentration
  bound for `f̂` when `f` vanishes outside `A`.
* `card_le_mul_card_filter_support` : the Donoho–Stark bound
  `|G| ≤ |supp f| * |supp f̂|`.
* `eq_zero_of_card_mul_card_lt_card` : no nonzero `f` is supported in
  `A` with Fourier support in `B` when `|A| * |B| < |G|`.
-/

@[expose] public section

open scoped BigOperators
open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted

namespace MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A character takes values on the unit circle. -/
theorem norm_addChar_apply (ψ : AddChar G ℂ) (x : G) : ‖ψ x‖ = 1 := by
  have hstar : star (ψ x) = ψ (-x) := by
    rw [RCLike.star_def, AddChar.map_neg_eq_conj]
  have h1 : star (ψ x) * ψ x = 1 := by
    rw [hstar, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : ‖ψ x‖ ^ 2 = 1 := by
    have hnorm : ‖star (ψ x) * ψ x‖ = 1 := by rw [h1]; simp
    rw [norm_mul, norm_star] at hnorm
    nlinarith [hnorm]
  rcases (sq_eq_one_iff.mp h2) with h | h
  · exact h
  · exfalso
    have := norm_nonneg (ψ x)
    rw [h] at this
    norm_num at this

/-- Plancherel in squared-norm form: the squared `ℓ²` norm of `f̂` is
`|G|` times the squared `ℓ²` norm of `f`. -/
theorem sum_norm_sq_dftFun (f : G → ℂ) :
    ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2
      = (Fintype.card G : ℝ) * ∑ x : G, ‖f x‖ ^ 2 := by
  have h := dft_plancherel f f
  have h1 : ∀ z : ℂ, star z * z = ((‖z‖ : ℂ)) ^ 2 := by
    intro z
    rw [RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [Finset.sum_congr rfl (fun x _ => h1 (f x)),
    Finset.sum_congr rfl (fun ψ _ => h1 (dftFun f ψ))] at h
  have hN : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h2 : (∑ ψ : AddChar G ℂ, ((‖dftFun f ψ‖ : ℂ)) ^ 2) =
      (Fintype.card G : ℂ) * ∑ x : G, ((‖f x‖ : ℂ)) ^ 2 := by
    calc (∑ ψ : AddChar G ℂ, ((‖dftFun f ψ‖ : ℂ)) ^ 2)
        = (Fintype.card G : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
            ∑ ψ : AddChar G ℂ, ((‖dftFun f ψ‖ : ℂ)) ^ 2) := by
          rw [mul_inv_cancel_left₀ hN]
      _ = (Fintype.card G : ℂ) * ∑ x : G, ((‖f x‖ : ℂ)) ^ 2 := by rw [← h]
  exact_mod_cast h2

/-- Cauchy–Schwarz in the form used below: the square of a sum over a
finset is at most the cardinality times the sum of squares. -/
private theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 2 ≤ s.card * ∑ i ∈ s, a i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s a (fun _ => (1 : ℝ))
  simpa [mul_comm] using h

/-- Pointwise bound: if `f̂` vanishes outside `B`, then each `‖f x‖²`
is at most `(|B| / |G|)` times the total squared `ℓ²` mass of `f`. -/
theorem norm_sq_le_of_dftFun_eq_zero_of_notMem {f : G → ℂ}
    {B : Finset (AddChar G ℂ)} (hB : ∀ ψ, ψ ∉ B → dftFun f ψ = 0) (x : G) :
    ‖f x‖ ^ 2 ≤ (B.card / Fintype.card G) * ∑ y : G, ‖f y‖ ^ 2 := by
  have hN : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ)
      = ∑ ψ ∈ B, star (ψ x) * dftFun f ψ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro ψ _ hψ
    simp [hB ψ hψ]
  have hfx : f x = (Fintype.card G : ℂ)⁻¹ *
      ∑ ψ ∈ B, star (ψ x) * dftFun f ψ := by
    rw [dft_inversion f x, hsum]
  set S : ℝ := ∑ ψ ∈ B, ‖dftFun f ψ‖ with hS
  have hnorm : ‖f x‖ ≤ (Fintype.card G : ℝ)⁻¹ * S := by
    rw [hfx, norm_mul]
    have h1 : ‖(Fintype.card G : ℂ)⁻¹‖ = (Fintype.card G : ℝ)⁻¹ := by
      simp [norm_inv]
    rw [h1]
    gcongr
    calc ‖∑ ψ ∈ B, star (ψ x) * dftFun f ψ‖
        ≤ ∑ ψ ∈ B, ‖star (ψ x) * dftFun f ψ‖ := norm_sum_le _ _
      _ = ∑ ψ ∈ B, ‖dftFun f ψ‖ := by
          apply Finset.sum_congr rfl
          intro ψ _
          rw [norm_mul, norm_star, norm_addChar_apply, one_mul]
  have hCS : S ^ 2 ≤ B.card * ((Fintype.card G : ℝ) * ∑ y : G, ‖f y‖ ^ 2) := by
    calc S ^ 2 ≤ B.card * ∑ ψ ∈ B, ‖dftFun f ψ‖ ^ 2 := sq_sum_le_card_mul_sum_sq B _
      _ ≤ B.card * ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
            (fun ψ _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
      _ = B.card * ((Fintype.card G : ℝ) * ∑ y : G, ‖f y‖ ^ 2) := by
          rw [sum_norm_sq_dftFun]
  calc ‖f x‖ ^ 2 ≤ ((Fintype.card G : ℝ)⁻¹ * S) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (Fintype.card G : ℝ)⁻¹ ^ 2 * S ^ 2 := by ring
    _ ≤ (Fintype.card G : ℝ)⁻¹ ^ 2 * (B.card * ((Fintype.card G : ℝ) * ∑ y : G, ‖f y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = (B.card / Fintype.card G) * ∑ y : G, ‖f y‖ ^ 2 := by
        field_simp

/-- Concentration of `f`: if `f̂` vanishes outside `B`, then the squared
`ℓ²` mass of `f` on any set `A` is at most `(|A| * |B| / |G|)` times the
total squared `ℓ²` mass of `f`. -/
theorem sum_norm_sq_le_of_dftFun_eq_zero_of_notMem {f : G → ℂ}
    {A : Finset G} {B : Finset (AddChar G ℂ)}
    (hB : ∀ ψ, ψ ∉ B → dftFun f ψ = 0) :
    ∑ x ∈ A, ‖f x‖ ^ 2 ≤ (A.card * B.card / Fintype.card G) * ∑ x : G, ‖f x‖ ^ 2 := by
  calc ∑ x ∈ A, ‖f x‖ ^ 2
      ≤ ∑ _x ∈ A, (B.card / Fintype.card G) * ∑ y : G, ‖f y‖ ^ 2 :=
        Finset.sum_le_sum (fun x _ => norm_sq_le_of_dftFun_eq_zero_of_notMem hB x)
    _ = A.card * ((B.card / Fintype.card G) * ∑ y : G, ‖f y‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (A.card * B.card / Fintype.card G) * ∑ x : G, ‖f x‖ ^ 2 := by
        field_simp

/-- Concentration of `f̂`: if `f` vanishes outside `A`, then the squared
`ℓ²` mass of `f̂` on any set `B` is at most `(|A| * |B| / |G|)` times the
total squared `ℓ²` mass of `f̂`. -/
theorem sum_norm_sq_dftFun_le_of_eq_zero_of_notMem {f : G → ℂ}
    {A : Finset G} {B : Finset (AddChar G ℂ)}
    (hA : ∀ x, x ∉ A → f x = 0) :
    ∑ ψ ∈ B, ‖dftFun f ψ‖ ^ 2
      ≤ (A.card * B.card / Fintype.card G) * ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 := by
  have hN : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  set SA : ℝ := ∑ x ∈ A, ‖f x‖ with hSA
  have hpoint : ∀ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ≤ SA := by
    intro ψ
    have hsum : dftFun f ψ = ∑ x ∈ A, ψ x * f x := by
      show (∑ x : G, ψ x * f x) = _
      symm
      apply Finset.sum_subset (Finset.subset_univ A)
      intro x _ hx
      simp [hA x hx]
    rw [hsum]
    calc ‖∑ x ∈ A, ψ x * f x‖ ≤ ∑ x ∈ A, ‖ψ x * f x‖ := norm_sum_le _ _
      _ = ∑ x ∈ A, ‖f x‖ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [norm_mul, norm_addChar_apply, one_mul]
  have hCS : SA ^ 2 ≤ A.card * ∑ x : G, ‖f x‖ ^ 2 := by
    calc SA ^ 2 ≤ A.card * ∑ x ∈ A, ‖f x‖ ^ 2 := sq_sum_le_card_mul_sum_sq A _
      _ ≤ A.card * ∑ x : G, ‖f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun x _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hPlan : ∑ x : G, ‖f x‖ ^ 2
      = (Fintype.card G : ℝ)⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 := by
    rw [sum_norm_sq_dftFun]
    field_simp
  calc ∑ ψ ∈ B, ‖dftFun f ψ‖ ^ 2
      ≤ ∑ _ψ ∈ B, SA ^ 2 :=
        Finset.sum_le_sum (fun ψ _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint ψ) 2)
    _ = B.card * SA ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B.card * (A.card * ((Fintype.card G : ℝ)⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [← hPlan]
        exact hCS
    _ = (A.card * B.card / Fintype.card G) * ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 := by
        field_simp

/-- The Donoho–Stark uncertainty principle: a nonzero function on a finite
abelian group and its Fourier transform cannot both have small support. -/
theorem card_le_mul_card_filter_support {f : G → ℂ} (hf : f ≠ 0) :
    Fintype.card G ≤
      (Finset.univ.filter (fun x => f x ≠ 0)).card *
        (Finset.univ.filter (fun ψ => dftFun f ψ ≠ 0)).card := by
  set A : Finset G := Finset.univ.filter (fun x => f x ≠ 0) with hA
  set B : Finset (AddChar G ℂ) := Finset.univ.filter (fun ψ => dftFun f ψ ≠ 0) with hB
  have hBvan : ∀ ψ, ψ ∉ B → dftFun f ψ = 0 := by
    intro ψ hψ
    by_contra hne
    exact hψ (Finset.mem_filter.mpr ⟨Finset.mem_univ ψ, hne⟩)
  have hsum : ∑ x ∈ A, ‖f x‖ ^ 2 = ∑ x : G, ‖f x‖ ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ A)
    intro x _ hx
    have : f x = 0 := by
      by_contra hne
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)
    simp [this]
  have hpos : 0 < ∑ x : G, ‖f x‖ ^ 2 := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
      by_contra h
      exact hf (funext fun x => by by_contra hx; exact h ⟨x, hx⟩)
    apply Finset.sum_pos' (fun x _ => sq_nonneg _)
    exact ⟨x₀, Finset.mem_univ x₀, pow_pos (norm_pos_iff.mpr hx₀) 2⟩
  have hconc := sum_norm_sq_le_of_dftFun_eq_zero_of_notMem (f := f) (A := A) (B := B) hBvan
  rw [hsum] at hconc
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have h1 : (1 : ℝ) ≤ (A.card * B.card / Fintype.card G) := by
    rwa [le_mul_iff_one_le_left hpos] at hconc
  have h2 : (Fintype.card G : ℝ) ≤ A.card * B.card := (one_le_div hN).mp h1
  exact_mod_cast h2

/-- Nonvanishing form: there is no nonzero function supported in `A`
whose Fourier transform is supported in `B` when `|A| * |B| < |G|`. -/
theorem eq_zero_of_card_mul_card_lt_card {f : G → ℂ}
    {A : Finset G} {B : Finset (AddChar G ℂ)}
    (hA : ∀ x, x ∉ A → f x = 0) (hB : ∀ ψ, ψ ∉ B → dftFun f ψ = 0)
    (h : A.card * B.card < Fintype.card G) : f = 0 := by
  by_contra hf
  have hcard := card_le_mul_card_filter_support hf
  have hsubA : (Finset.univ.filter (fun x => f x ≠ 0)).card ≤ A.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx
    by_contra hxA
    exact hx.2 (hA x hxA)
  have hsubB : (Finset.univ.filter (fun ψ => dftFun f ψ ≠ 0)).card ≤ B.card := by
    apply Finset.card_le_card
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    by_contra hψB
    exact hψ.2 (hB ψ hψB)
  have := mul_le_mul hsubA hsubB (Nat.zero_le _) (Nat.zero_le _)
  omega

end MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty
