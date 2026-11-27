/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Discriminant
import MathlibExt.NumberTheory.ModularForms.LatticeDiscriminantEta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Invariance of `|Δ(τ)| (Im τ)⁶` under the modular group

For `τ` in the upper half-plane, let `Δ(τ) = g₂(τ)³ - 27 g₃(τ)²` be the discriminant of the
lattice `ℤ τ + ℤ`. For integers `a, b, c, d` with `a d - b c = 1`, `Δ` transforms with weight
`12`, `Im` transforms by `|c τ + d|⁻²`, and so `|Δ(τ)| (Im τ)⁶` is invariant; the same holds for
`η²⁴` (`MetaMathlibExt.discriminant_im_pow_six_invariant`). The proof combines Jacobi's product
formula `MetaMathlibExt.lattice_discriminant_eq_eta_product` with Mathlib's cusp form
`CuspForm.discriminant` of weight `12` for `SL₂(ℤ)`.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>: Chapter V, §3, Proposition 3.5 and (3.1b), p. 191.
* P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]",
  Séminaire Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: Remarque 1.5, p. 28.
-/

@[expose] public section

namespace MetaMathlibExt

open ModularForm UpperHalfPlane
open scoped Real MatrixGroups

/-- The imaginary part of `(a τ + b) / (c τ + d)` for `a d - b c = 1`. -/
private lemma im_div_eq (τ : ℂ) (a b c d : ℤ) (h : a * d - b * c = 1) :
    ((a * τ + b) / (c * τ + d)).im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq]
  have hdet : ((a : ℝ) * d - b * c) = 1 := by exact_mod_cast h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, add_zero]
  rw [div_sub_div_same]
  congr 1
  linear_combination τ.im * hdet

/-- **Invariance of `|Δ(τ)| (Im τ)⁶` under the modular group.** For `τ` in the upper half-plane
let `Δ(τ) = g₂(τ)³ - 27 g₃(τ)²` be the discriminant of the lattice `ℤ τ + ℤ`, where `g₂(τ)` is
sixty times the sum of the inverse fourth powers of the nonzero periods `m τ + n` and `g₃(τ)` is
one hundred forty times the sum of their inverse sixth powers (as in
`MetaMathlibExt.lattice_discriminant_eq_eta_product`, where the sums run over all integer
pairs and the summand of the zero pair is zero).
Then for all integers `a, b, c, d` with `a d - b c = 1`,
`Δ((a τ + b) / (c τ + d)) = (c τ + d)¹² Δ(τ)` and
`Im((a τ + b) / (c τ + d)) = Im τ / |c τ + d|²`, and hence
`|Δ((a τ + b) / (c τ + d))| Im((a τ + b) / (c τ + d))⁶ = |Δ(τ)| (Im τ)⁶`. The same holds with
`η²⁴` in place of `Δ`, for the Dedekind eta function `η`.

Sources: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's
version <https://jmilne.org/math/Books/EC2.pdf>, Chapter V, §3, Proposition 3.5, p. 191:
`Δ = g₄³ - 27 g₆²` is a cusp form of weight 12 for `Γ₀(1)`, with the transformation law (3.1b),
p. 191; P. Deligne, Séminaire Bourbaki, exposé 616, Astérisque 121–122 (1985),
<http://www.numdam.org/item/SB_1983-1984__26__25_0/>, Remarque 1.5, p. 28: the function
`4π y |q^{1/12} ∏ (1 - qⁿ)²|²`, `y = Im(τ)`, is invariant under `SL(2, ℤ)`. -/
theorem discriminant_im_pow_six_invariant (τ : ℍ) (a b c d : ℤ) (h : a * d - b * c = 1) :
    let Δ : ℂ → ℂ := fun z ↦
      (60 * ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * z + v 1) ^ 4)⁻¹) ^ 3 -
        27 * (140 * ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * z + v 1) ^ 6)⁻¹) ^ 2
    let w : ℂ := (a * τ + b) / (c * τ + d)
    Δ w = (c * τ + d) ^ 12 * Δ τ ∧
      w.im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 ∧
      ‖Δ w‖ * w.im ^ 6 = ‖Δ τ‖ * τ.im ^ 6 ∧
      eta w ^ 24 = (c * τ + d) ^ 12 * eta τ ^ 24 ∧
      ‖eta w ^ 24‖ * w.im ^ 6 = ‖eta τ ^ 24‖ * τ.im ^ 6 := by
  intro Δ w
  let g : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩
  let γ := Matrix.SpecialLinearGroup.mapGL ℝ g
  have hγ : γ ∈ (Matrix.SpecialLinearGroup.mapGL ℝ).range := ⟨g, rfl⟩
  have e : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) :=
    fun _ _ ↦ rfl
  have hdet : (0 : ℝ) < (Matrix.GeneralLinearGroup.det γ : ℝ) := by
    simp [γ, Matrix.SpecialLinearGroup.mapGL]
  have hw : ((γ • τ : ℍ) : ℂ) = w := by
    rw [coe_smul_of_det_pos hdet]
    simp [e, g, num, denom, w]
  have hcd : (c : ℂ) * τ + d ≠ 0 := by
    have := denom_ne_zero γ τ
    simpa [e, g, denom] using this
  -- the transformation law of `η²⁴`
  have heta : eta w ^ 24 = (c * τ + d) ^ 12 * eta τ ^ 24 := by
    have hf := SlashInvariantForm.slash_action_eqn' CuspForm.discriminant hγ τ
    rw [CuspForm.coe_discriminant] at hf
    simp only [discriminant, hw] at hf
    simpa [e, g] using hf
  -- Jacobi's product formula at `w` and at `τ`
  have hΔw : Δ w = (2 * π : ℂ) ^ 12 * eta w ^ 24 := by
    have := (lattice_discriminant_eq_eta_product (γ • τ)).1
    rw [hw] at this
    exact this
  have hΔτ : Δ τ = (2 * π : ℂ) ^ 12 * eta τ ^ 24 := (lattice_discriminant_eq_eta_product τ).1
  have him : w.im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 := im_div_eq τ a b c d h
  have hnorm : ‖(c : ℂ) * τ + d‖ ≠ 0 := norm_ne_zero_iff.mpr hcd
  have hinv : ∀ f : ℂ → ℂ, f w = (c * τ + d) ^ 12 * f τ →
      ‖f w‖ * w.im ^ 6 = ‖f τ‖ * τ.im ^ 6 := by
    intro f hf
    rw [hf, him, norm_mul, norm_pow, div_pow]
    field_simp
  have hΔ : Δ w = (c * τ + d) ^ 12 * Δ τ := by
    rw [hΔw, hΔτ, heta]
    ring
  exact ⟨hΔ, him, hinv Δ hΔ, heta, hinv (fun z ↦ eta z ^ 24) heta⟩

end MetaMathlibExt
