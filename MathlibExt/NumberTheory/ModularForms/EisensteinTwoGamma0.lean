/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Definitions/Def_ModularCurve_EisensteinTwoCoeff.lean`,
`Theorems/Thm_ModularCurve_eisensteinTwoSlash_slash_eq_self.lean`,
`Theorems/Thm_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash.lean`,
`Theorems/Thm_ModularCurve_hasSum_eisensteinTwoCoeff_mul_cexp_pow.lean`,
`Theorems/Thm_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff.lean`,
`P2M/Sol/S_ModularCurve_eisensteinTwoSlash_slash_eq_self.lean`,
`P2M/Sol/S_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash.lean`,
`P2M/Sol/S_ModularCurve_hasSum_eisensteinTwoCoeff_mul_cexp_pow.lean` and
`P2M/Sol/S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.OldForms
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.QExpansion
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

/-!
# The weight-two Eisenstein form on `Γ₀(p)`

The weight-two Eisenstein series `E₂` is not modular, but for `p ≠ 0` the combination
`E₂ ∣[2] diag(p, 1) - E₂`, i.e. `τ ↦ p E₂(pτ) - E₂(τ)`, is a modular form of weight two
on `Γ₀(p)`. Its `q`-expansion has constant term `p - 1` and `n`-th coefficient
`24 σ'_p(n)`, where `σ'_p(n)` is the sum of the divisors of `n` not divisible by `p`.

## Main definitions

* `ModularForm.sigmaPrimeTo p n`: the sum of the divisors of `n` not divisible by `p`.
* `ModularForm.eisensteinTwoCoeff p n`: the `n`-th `q`-coefficient of the form.
* `ModularForm.eisensteinTwoGamma0 p`: the modular form `p E₂(pτ) - E₂(τ)` on `Γ₀(p)`.

## Main results

* `ModularForm.qCoeff_eisensteinTwoGamma0`: its `q`-coefficients are `eisensteinTwoCoeff p`.
* `ModularForm.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff`.

## References

* B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977), 33–186,
  Chapter II, (5.1): the `q`-expansion `e'` of the weight-two Eisenstein series on `Γ₀(N)`,
  which is `-1` times the form here.
-/

@[expose] public section

open UpperHalfPlane hiding I σ
open CongruenceSubgroup Matrix Complex
open scoped MatrixGroups ModularForm Manifold Real ArithmeticFunction.sigma

noncomputable section

namespace ModularForm

/-- The sum of the divisors of `n` that are not divisible by `p`; it is `0` for `n = 0`, which
has no divisors in Mathlib's convention. -/
def sigmaPrimeTo (p n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), d

/-- The integer `p - 1` for `n = 0` and `24 σ'_p(n)` for `n ≥ 1`, where `σ'_p(n)` is the sum of
the divisors of `n` not divisible by `p`. For `p ≠ 0` these are the `q`-coefficients of the
weight-two Eisenstein form `p E₂(pτ) - E₂(τ)` on `Γ₀(p)`. -/
def eisensteinTwoCoeff (p n : ℕ) : ℤ :=
  if n = 0 then (p : ℤ) - 1 else 24 * (sigmaPrimeTo p n : ℤ)

/-- For every `p`, the coefficient `eisensteinTwoCoeff p 0` is `p - 1`. -/
theorem eisensteinTwoCoeff_zero (p : ℕ) : eisensteinTwoCoeff p 0 = (p : ℤ) - 1 := by
  simp [eisensteinTwoCoeff]

/-- For every `p` and `n ≠ 0`, the coefficient `eisensteinTwoCoeff p n` is `24 σ'_p(n)`, where
`σ'_p(n)` is the sum of the divisors of `n` not divisible by `p`. -/
theorem eisensteinTwoCoeff_of_ne_zero (p : ℕ) {n : ℕ} (hn : n ≠ 0) :
    eisensteinTwoCoeff p n = 24 * (sigmaPrimeTo p n : ℤ) := by
  simp [eisensteinTwoCoeff, hn]

/-! ### Invariance under `Γ₀(p)` -/

private theorem sub_slash' (k : ℤ) (B : GL (Fin 2) ℝ) (f g : ℍ → ℂ) :
    (f - g) ∣[k] B = f ∣[k] B - g ∣[k] B := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

private theorem slash_mapGL' (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] (SpecialLinearGroup.mapGL ℝ γ) = f ∣[k] γ := rfl

private theorem conj_det (p : ℕ) (γ : SL(2, ℤ)) (hc : (p : ℤ) ∣ γ 1 0) :
    det !![γ 0 0, (p : ℤ) * γ 0 1; γ 1 0 / (p : ℤ), γ 1 1] = 1 := by
  have h1 : (p : ℤ) * (γ 1 0 / (p : ℤ)) = γ 1 0 := Int.mul_ediv_cancel' hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h2 := γ.2
    rwa [det_fin_two] at h2
  rw [det_fin_two_of]
  have hb : (p : ℤ) * γ 0 1 * (γ 1 0 / (p : ℤ)) = γ 0 1 * γ 1 0 := by
    rw [mul_comm (p : ℤ) (γ 0 1), mul_assoc, h1]
  omega

private theorem val_heckeDiagMatrix_eq_map (p : ℕ) (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![(p : ℤ), 0; 0, 1]).map (algebraMap ℤ ℝ) := by
  rw [val_heckeDiagMatrix hp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_mapGL_eq_map (γ : SL(2, ℤ)) :
    ((SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl

private theorem heckeDiag_mul_mapGL (p : ℕ) (hp : p ≠ 0) (γ γ' : SL(2, ℤ))
    (hZ : !![(p : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1]) :
    heckeDiagMatrix p * SpecialLinearGroup.mapGL ℝ γ
      = SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix_eq_map p hp,
    coe_mapGL_eq_map, coe_mapGL_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hZ]

private theorem D2_slash_heckeDiag (p : ℕ) (hp : p ≠ 0) (γ γ' : SL(2, ℤ))
    (h10 : (γ' 1 0 : ℤ) = γ 1 0 / (p : ℤ)) (h11 : (γ' 1 1 : ℤ) = γ 1 1)
    (hc : (p : ℤ) ∣ γ 1 0) :
    (EisensteinSeries.D2 γ') ∣[(2 : ℤ)] heckeDiagMatrix p = EisensteinSeries.D2 γ := by
  ext τ
  rw [slash_heckeDiagMatrix_apply _ hp]
  simp only [EisensteinSeries.D2]
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply, coe_heckeDiagMatrix_smul hp]
  have hdiv : ((γ 1 0 / (p : ℤ) : ℤ) : ℂ) * (p : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.ediv_mul_cancel hc)
  have h10' : ((γ' 1 0 : ℤ) : ℂ) = ((γ 1 0 / (p : ℤ) : ℤ) : ℂ) := by exact_mod_cast h10
  have h11' : ((γ' 1 1 : ℤ) : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by exact_mod_cast h11
  rw [h10', h11', show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, ← mul_assoc, hdiv,
    mul_div_assoc']
  congr 1
  linear_combination (2 * (π : ℂ) * I) * hdiv

/-- For `p ≠ 0` (`[NeZero p]`), the function `E₂ ∣[2] diag(p, 1) - E₂`, that is
`τ ↦ p E₂(pτ) - E₂(τ)`, is invariant under the weight-two slash action of `Γ₀(p)`. -/
theorem eisensteinTwoSlash_slash_eq_self (p : ℕ) [NeZero p] :
    ∀ γ ∈ ((Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      (EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ
        = EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p - EisensteinSeries.E2 := by
  have hp : p ≠ 0 := NeZero.ne p
  intro γ hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
  have hc : (p : ℤ) ∣ γ₀ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (Gamma0_mem.mp hγ₀)
  obtain ⟨γ', h10, h11, hval⟩ :
      ∃ γ' : SL(2, ℤ),
        (γ' 1 0 : ℤ) = γ₀ 1 0 / (p : ℤ) ∧ (γ' 1 1 : ℤ) = γ₀ 1 1 ∧
          (γ' : Matrix (Fin 2) (Fin 2) ℤ)
            = !![γ₀ 0 0, (p : ℤ) * γ₀ 0 1; γ₀ 1 0 / (p : ℤ), γ₀ 1 1] :=
    ⟨⟨!![γ₀ 0 0, (p : ℤ) * γ₀ 0 1; γ₀ 1 0 / (p : ℤ), γ₀ 1 1], conj_det p γ₀ hc⟩,
      rfl, rfl, rfl⟩
  have hZ : !![(p : ℤ), 0; 0, 1] * (γ₀ : Matrix (Fin 2) (Fin 2) ℤ)
      = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1] := by
    rw [hval]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Int.ediv_mul_cancel hc, mul_comm]
  have hconj := heckeDiag_mul_mapGL p hp γ₀ γ' hZ
  rw [sub_slash', ← SlashAction.slash_mul, hconj, SlashAction.slash_mul,
    slash_mapGL', slash_mapGL',
    EisensteinSeries.E2_slash_action γ', EisensteinSeries.E2_slash_action γ₀,
    sub_slash', ModularForm.smul_slash, σ_heckeDiagMatrix,
    D2_slash_heckeDiag p hp γ₀ γ' h10 h11 hc]
  simp only [ContinuousAlgEquiv.refl_apply]
  abel

/-! ### Boundedness at the cusps -/

/-- For every `γ ∈ SL(2, ℤ)`, the correction term `D₂ γ` in the transformation law of `E₂` is
bounded at `i∞`. -/
theorem _root_.EisensteinSeries.isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (EisensteinSeries.D2 γ) := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hD : EisensteinSeries.D2 γ = 0 := by
      funext z
      simp [EisensteinSeries.D2, hc]
    rw [hD]
    exact zero_form_isBoundedAtImInfty
  · rw [isBoundedAtImInfty_iff]
    refine ⟨‖2 * (π : ℂ) * I * ((γ 1 0 : ℤ) : ℂ)‖, 1, fun z hz => ?_⟩
    have him : (denom γ z).im = ((γ 1 0 : ℤ) : ℝ) * z.im := by
      rw [ModularGroup.denom_apply]
      simp
    have hc1 : (1 : ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hc
    have hlow : |((γ 1 0 : ℤ) : ℝ)| ≤ ‖denom γ z‖ :=
      calc |((γ 1 0 : ℤ) : ℝ)| = |((γ 1 0 : ℤ) : ℝ)| * 1 := (mul_one _).symm
        _ ≤ |((γ 1 0 : ℤ) : ℝ)| * z.im := by gcongr
        _ = |((γ 1 0 : ℤ) : ℝ) * z.im| := by
            rw [abs_mul, abs_of_pos z.im_pos]
        _ = |(denom γ z).im| := by rw [him]
        _ ≤ ‖denom γ z‖ := Complex.abs_im_le_norm _
    have hone : (1 : ℝ) ≤ ‖denom γ z‖ := hc1.trans hlow
    change ‖(2 * (π : ℂ) * I * ((γ 1 0 : ℤ) : ℂ)) / denom γ z‖ ≤ _
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hone

/-- For every `γ ∈ SL(2, ℤ)`, the weight-two slash `E₂ ∣[2] γ` is bounded at `i∞`. -/
theorem _root_.EisensteinSeries.isBoundedAtImInfty_E2_slash (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) := by
  rw [EisensteinSeries.E2_slash_action, sub_eq_add_neg]
  exact EisensteinSeries.isBoundedAtImInfty_E2.add
    ((EisensteinSeries.isBoundedAtImInfty_D2 γ).smul _).neg

private lemma isBoundedAtImInfty_E2_slash_of_row (g : GL (Fin 2) ℝ) (N : SL(2, ℤ))
    (hN : (SpecialLinearGroup.mapGL ℝ N * g) 1 0 = 0) :
    IsBoundedAtImInfty (EisensteinSeries.E2 ∣[(2 : ℤ)] g) := by
  have h1 : IsBoundedAtImInfty
      (EisensteinSeries.E2 ∣[(2 : ℤ)] SpecialLinearGroup.mapGL ℝ N⁻¹) :=
    EisensteinSeries.isBoundedAtImInfty_E2_slash N⁻¹
  have h2 := h1.slash (2 : ℤ) hN
  rwa [← SlashAction.slash_mul, map_inv, inv_mul_cancel_left] at h2

private lemma exists_row_zero (p : ℕ) (hp : p ≠ 0) (γ : SL(2, ℤ)) :
    ∃ N : SL(2, ℤ), (SpecialLinearGroup.mapGL ℝ N *
      (heckeDiagMatrix p * SpecialLinearGroup.mapGL ℝ γ)) 1 0 = 0 := by
  have hentry : ∀ N : SL(2, ℤ), (SpecialLinearGroup.mapGL ℝ N *
      (heckeDiagMatrix p * SpecialLinearGroup.mapGL ℝ γ)) 1 0
      = ((N 1 0 : ℤ) : ℝ) * ((p : ℝ) * ((γ 0 0 : ℤ) : ℝ))
        + ((N 1 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
    intro N
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      val_heckeDiagMatrix hp, SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map_apply, algebraMap_int_eq, Int.coe_castRingHom, Matrix.vecMul, dotProduct]
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · refine ⟨1, ?_⟩
    rw [hentry 1]
    simp [hc]
  · have hpos : 0 < Int.gcd ((p : ℤ) * γ 0 0) (γ 1 0) :=
      Nat.pos_of_ne_zero fun h => hc (Int.gcd_eq_zero_iff.mp h).2
    obtain ⟨a', c', hcop, ha, hcc⟩ := Int.exists_gcd_one hpos
    have hmem : (![-c', a'] : Fin 2 → ℤ) ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} := by
      simpa using (Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm.neg_left
    obtain ⟨N, -, hN⟩ := ModularGroup.bottom_row_surj hmem
    have hN0 : N 1 0 = -c' := by simpa using congrFun hN 0
    have hN1 : N 1 1 = a' := by simpa using congrFun hN 1
    have hz0 : -c' * ((p : ℤ) * γ 0 0) + a' * γ 1 0 = 0 := by
      set G : ℤ := (Int.gcd ((p : ℤ) * γ 0 0) (γ 1 0) : ℤ)
      rw [ha, hcc]
      ring
    refine ⟨N, ?_⟩
    rw [hentry N, hN0, hN1]
    exact_mod_cast hz0

/-- For `p ≠ 0` (`[NeZero p]`) and every `γ ∈ SL(2, ℤ)`, the weight-two slash by `γ` of
`E₂ ∣[2] diag(p, 1) - E₂` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_eisensteinTwoSlash_slash (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty
      ((EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hAγ : (EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p) ∣[(2 : ℤ)] γ
      = EisensteinSeries.E2 ∣[(2 : ℤ)]
        (heckeDiagMatrix p * SpecialLinearGroup.mapGL ℝ γ) := by
    rw [SlashAction.slash_mul]
    rfl
  obtain ⟨N, hN⟩ := exists_row_zero p hp γ
  have h1 : IsBoundedAtImInfty
      ((EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p) ∣[(2 : ℤ)] γ) := by
    rw [hAγ]
    exact isBoundedAtImInfty_E2_slash_of_row _ N hN
  rw [← slash_mapGL', sub_slash', slash_mapGL', slash_mapGL', sub_eq_add_neg]
  exact h1.add (EisensteinSeries.isBoundedAtImInfty_E2_slash γ).neg

/-! ### The `q`-expansion -/

private lemma summable_sigma_mul_cexp_pow' (z : ℍ) :
    Summable fun n : ℕ => (σ 1 n : ℂ) * cexp (2 * π * I * z) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one 2 (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 n).trans_eq (by norm_num)

private lemma hasSum_sigma_succ_mul_cexp_pow (z : ℍ) :
    HasSum (fun n : ℕ => (σ 1 (n + 1) : ℂ) * cexp (2 * π * I * z) ^ (n + 1))
      ((1 - EisensteinSeries.E2 z) / 24) := by
  have hs : Summable fun n : ℕ =>
      (σ 1 (n + 1) : ℂ) * cexp (2 * π * I * z) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow' z)
  rw [hs.hasSum_iff, ← tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => (σ 1 n : ℂ) * cexp (2 * π * I * z) ^ n),
    EisensteinSeries.E2_eq_tsum_cexp z]
  ring

private lemma sigma_one_eq_sigmaPrimeTo_add (p n : ℕ) (hp : p ≠ 0) (hn : n ≠ 0)
    (hpn : p ∣ n) : σ 1 n = sigmaPrimeTo p n + p * σ 1 (n / p) := by
  have hnp : n / p ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hp, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn⟩
  have himg : n.divisors.filter (fun d => p ∣ d) = (n / p).divisors.image (fun e => p * e) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hdn, -⟩, e, rfl⟩
      exact ⟨e, ⟨(Nat.dvd_div_iff_mul_dvd hpn).mpr hdn, hnp⟩, rfl⟩
    · rintro ⟨e, ⟨hednp, -⟩, rfl⟩
      exact ⟨⟨(Nat.dvd_div_iff_mul_dvd hpn).mp hednp, hn⟩, ⟨e, rfl⟩⟩
  have hinj : ∀ x ∈ (n / p).divisors, ∀ y ∈ (n / p).divisors, p * x = p * y → x = y :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h
  have hσ : σ 1 n = ∑ d ∈ n.divisors, d := by
    simp [ArithmeticFunction.sigma_one_apply]
  have hσ' : σ 1 (n / p) = ∑ d ∈ (n / p).divisors, d := by
    simp [ArithmeticFunction.sigma_one_apply]
  rw [hσ, hσ', ← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => ¬ p ∣ d)]
  have hrw : n.divisors.filter (fun d => ¬ ¬ p ∣ d) = n.divisors.filter (fun d => p ∣ d) := by
    simp
  rw [hrw, himg, Finset.sum_image hinj, ← Finset.mul_sum]
  simp only [sigmaPrimeTo]

private lemma sigmaPrimeTo_eq_sigma_one (p n : ℕ) (hpn : ¬ p ∣ n) :
    sigmaPrimeTo p n = σ 1 n := by
  simp only [ArithmeticFunction.sigma_one_apply, sigmaPrimeTo]
  congr 1
  exact Finset.filter_true_of_mem fun d hd hpd =>
    hpn (hpd.trans (Nat.mem_divisors.mp hd).1)

private lemma hasSum_zero_extension_of_dvd {p : ℕ} (hp : p ≠ 0) (c : ℕ → ℂ) (q : ℂ) (s : ℂ)
    (h : HasSum (fun n : ℕ => c (n + 1) * q ^ (p * (n + 1))) s) :
    HasSum (fun n : ℕ => if p ∣ (n + 1) then c ((n + 1) / p) * q ^ (n + 1) else 0) s := by
  have hg : Function.Injective (fun n : ℕ => p * n + (p - 1)) := by
    intro a b hab
    have hab' : p * a + (p - 1) = p * b + (p - 1) := hab
    have h1 : p * a = p * b := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h1
  have hvanish : ∀ x, x ∉ Set.range (fun n : ℕ => p * n + (p - 1)) →
      (if p ∣ (x + 1) then c ((x + 1) / p) * q ^ (x + 1) else 0) = 0 := by
    intro x hx
    rw [ite_eq_right]
    rintro ⟨m, hm⟩
    apply hx
    rcases m with - | m'
    · exact absurd hm (by omega)
    · refine ⟨m', ?_⟩
      rw [Nat.mul_succ] at hm
      change p * m' + (p - 1) = x
      omega
  refine (Function.Injective.hasSum_iff hg hvanish).mp ?_
  have hcomp : ((fun n : ℕ => if p ∣ (n + 1) then c ((n + 1) / p) * q ^ (n + 1) else 0) ∘
      (fun n : ℕ => p * n + (p - 1))) = fun n : ℕ => c (n + 1) * q ^ (p * (n + 1)) := by
    funext n
    have h1 : p * n + (p - 1) + 1 = p * (n + 1) := by
      rw [Nat.mul_succ]
      omega
    simp only [Function.comp_apply, h1]
    rw [ite_eq_left (dvd_mul_right p (n + 1)), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
  rw [hcomp]
  exact h

/-- For `p ≠ 0` (`[NeZero p]`) and `τ` in the upper half-plane, the series
`∑ n, eisensteinTwoCoeff p n * q ^ n` with `q = exp(2πiτ)` converges to `p E₂(pτ) - E₂(τ)`. -/
theorem hasSum_eisensteinTwoCoeff_mul_cexp_pow (p : ℕ) [NeZero p] (τ : ℍ) :
    HasSum (fun n : ℕ => (eisensteinTwoCoeff p n : ℂ) * cexp (2 * π * I * τ) ^ n)
      ((p : ℂ) * EisensteinSeries.E2 (heckeDiagMatrix p • τ) - EisensteinSeries.E2 τ) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hsmul : ((heckeDiagMatrix p • τ : ℍ) : ℂ) = (p : ℂ) * (τ : ℂ) :=
    coe_heckeDiagMatrix_smul hp τ
  have hqp : cexp (2 * π * I * ((heckeDiagMatrix p • τ : ℍ) : ℂ)) =
      cexp (2 * π * I * (τ : ℂ)) ^ p := by
    rw [hsmul, show 2 * (π : ℂ) * I * ((p : ℂ) * (τ : ℂ)) =
        (p : ℂ) * (2 * (π : ℂ) * I * (τ : ℂ)) by ring, Complex.exp_nat_mul]
  have h₁ := (hasSum_sigma_succ_mul_cexp_pow τ).mul_left 24
  have h₂ := (hasSum_sigma_succ_mul_cexp_pow (heckeDiagMatrix p • τ)).mul_left (24 * (p : ℂ))
  simp only [hqp, ← pow_mul, ← mul_assoc] at h₂
  have h₂' := hasSum_zero_extension_of_dvd hp
      (fun m : ℕ => 24 * (p : ℂ) * (σ 1 m : ℂ)) (cexp (2 * π * I * τ)) _ h₂
  rw [← hasSum_nat_add_iff' 1]
  convert h₁.sub h₂' using 1
  · funext n
    by_cases hdvd : p ∣ (n + 1)
    · simp only [eisensteinTwoCoeff_of_ne_zero p (show n + 1 ≠ 0 from Nat.succ_ne_zero n),
        ite_eq_left hdvd]
      have hsplit : (σ 1 (n + 1) : ℂ) = (sigmaPrimeTo p (n + 1) : ℂ) +
          (p : ℂ) * (σ 1 ((n + 1) / p) : ℂ) := by
        exact_mod_cast sigma_one_eq_sigmaPrimeTo_add p (n + 1) hp (Nat.succ_ne_zero n) hdvd
      rw [hsplit]
      push_cast
      ring
    · simp only [eisensteinTwoCoeff_of_ne_zero p (show n + 1 ≠ 0 from Nat.succ_ne_zero n),
        ite_eq_right hdvd, sub_zero, sigmaPrimeTo_eq_sigma_one p (n + 1) hdvd]
      push_cast
      ring
  · simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
      eisensteinTwoCoeff_zero]
    push_cast
    ring

/-! ### The modular form -/

/-- For every `p`, the function `E₂ ∣[2] heckeDiagMatrix p - E₂` is holomorphic on the upper
half-plane; `heckeDiagMatrix p` is `diag(p, 1)` for `p ≠ 0` and `1` for `p = 0`. -/
theorem mdifferentiable_eisensteinTwoSlash (p : ℕ) :
    MDiff (EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p - EisensteinSeries.E2) :=
  (E2_mdifferentiable.slash 2 (heckeDiagMatrix p)).sub E2_mdifferentiable

/-- For `p ≠ 0` (`[NeZero p]`), the function `E₂ ∣[2] diag(p, 1) - E₂` is bounded in weight
two at every cusp of `Γ₀(p)`. -/
theorem isBoundedAt_eisensteinTwoSlash (p : ℕ) [NeZero p] {c : OnePoint ℝ}
    (hc : IsCusp c (Gamma0 p)) :
    c.IsBoundedAt (EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p - EisensteinSeries.E2) 2 := by
  have hc' : IsCusp c 𝒮ℒ := hc.mono (Subgroup.map_le_range _ _)
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
  intro γ _
  exact isBoundedAtImInfty_eisensteinTwoSlash_slash p γ

/-- For `p ≠ 0` (`[NeZero p]`), the weight-two Eisenstein form `p E₂(pτ) - E₂(τ)` on
`Γ₀(p)`. -/
noncomputable def eisensteinTwoGamma0 (p : ℕ) [NeZero p] : ModularForm (Gamma0 p) 2 where
  toFun := EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p - EisensteinSeries.E2
  slash_action_eq' := eisensteinTwoSlash_slash_eq_self p
  holo' := mdifferentiable_eisensteinTwoSlash p
  bdd_at_cusps' hc := isBoundedAt_eisensteinTwoSlash p hc

/-- For `p ≠ 0` (`[NeZero p]`), the underlying function of `eisensteinTwoGamma0 p` is
`E₂ ∣[2] diag(p, 1) - E₂`. -/
@[simp]
theorem coe_eisensteinTwoGamma0 (p : ℕ) [NeZero p] :
    ⇑(eisensteinTwoGamma0 p) =
      EisensteinSeries.E2 ∣[(2 : ℤ)] heckeDiagMatrix p - EisensteinSeries.E2 :=
  rfl

/-- For `p ≠ 0` (`[NeZero p]`) and `τ` in the upper half-plane,
`eisensteinTwoGamma0 p τ = p E₂(pτ) - E₂(τ)`. -/
theorem eisensteinTwoGamma0_apply (p : ℕ) [NeZero p] (τ : ℍ) :
    eisensteinTwoGamma0 p τ =
      (p : ℂ) * EisensteinSeries.E2 (heckeDiagMatrix p • τ) - EisensteinSeries.E2 τ := by
  rw [coe_eisensteinTwoGamma0, Pi.sub_apply, slash_heckeDiagMatrix_apply 2 (NeZero.ne p)]
  norm_num

/-- For `p ≠ 0` (`[NeZero p]`), the `q`-coefficients of `eisensteinTwoGamma0 p` are
`eisensteinTwoCoeff p n`: `p - 1` for `n = 0` and `24 σ'_p(n)` for `n ≥ 1`, where `σ'_p(n)` is the
sum of the divisors of `n` not divisible by `p`. -/
theorem qCoeff_eisensteinTwoGamma0 (p : ℕ) [NeZero p] (n : ℕ) :
    ModularFormClass.qCoeff (eisensteinTwoGamma0 p) n = (eisensteinTwoCoeff p n : ℂ) := by
  rw [ModularFormClass.qCoeff_eq]
  symm
  refine ModularFormClass.qExpansion_coeff_unique (h := 1)
    (c := fun m => (eisensteinTwoCoeff p m : ℂ)) one_pos
    (one_mem_strictPeriods_Gamma0 p) (f := eisensteinTwoGamma0 p) ?_ n
  intro τ
  have h := hasSum_eisensteinTwoCoeff_mul_cexp_pow p τ
  rw [← eisensteinTwoGamma0_apply p τ] at h
  have hq : Function.Periodic.qParam (1 : ℝ) (τ : ℂ) = cexp (2 * π * I * τ) := by
    simp [Function.Periodic.qParam]
  simpa [hq, smul_eq_mul] using h

/-- For a prime `p`, some weight-two modular form on `Γ₀(p)` has `q`-coefficients
`eisensteinTwoCoeff p n`: `p - 1` for `n = 0` and `24 σ'_p(n)` for `n ≥ 1`, where `σ'_p(n)` is the
sum of the divisors of `n` not divisible by `p`. -/
theorem exists_modularForm_qCoeff_eq_eisensteinTwoCoeff (p : ℕ) [Fact p.Prime] :
    ∃ E : ModularForm (Gamma0 p) 2,
      ∀ n : ℕ, ModularFormClass.qCoeff E n = (eisensteinTwoCoeff p n : ℂ) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ⟨eisensteinTwoGamma0 p, qCoeff_eisensteinTwoGamma0 p⟩

end ModularForm
