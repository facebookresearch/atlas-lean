/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CuspForm_AtkinLehnerOperator.lean`,
`Theorems/Thm_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0.lean`,
`P2M/Sol/S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0.lean`,
`P2M/Sol/S_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean` and
`P2M/Sol/S_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The Fricke involution on modular forms of level `Γ₀(N)`

For `N ≠ 0`, the Fricke matrix `W_N = !![0, -1; N, 0]` normalizes `Γ₀(N)`, so slashing by it
maps modular forms of weight `k` and level `Γ₀(N)` to modular forms of the same
weight and level. Its square is the scalar matrix `-N`, so applying the Fricke
operator twice multiplies by `(-1) ^ k * N ^ (k - 2)`.

## Main definitions and results

* `ModularForm.frickeGL N`: the Fricke matrix in `GL (Fin 2) ℝ`.
* `ModularForm.slash_scalar_natCast`: slashing by the scalar matrix `N` multiplies
  by `N ^ (k - 2)`.
* `ModularForm.fricke N k`: the Fricke operator as a linear map on
  `ModularForm (Gamma0 N) k`.
* `ModularForm.slash_frickeGL_slash_frickeGL`: `f ∣ W_N ∣ W_N = (-1) ^ k N ^ (k - 2) f`.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
* B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977), 33–186,
  Chapter II, §6 (the involution `w` induced by `z ↦ -1/(Nz)`).
-/

@[expose] public section

open Matrix UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularForm

/-- For `N ≠ 0`, slashing a function `g : ℍ → ℂ` in weight `k` by the scalar matrix `N`
multiplies it by `N ^ (k - 2)`. -/
theorem slash_scalar_natCast (k : ℤ) {N : ℕ} (hN : (N : ℝ) ≠ 0) (g : ℍ → ℂ) :
    g ∣[k] (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (N : ℝ) hN))
      = (N : ℂ) ^ (k - 2) • g := by
  ext τ
  have hdet : ((GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (N : ℝ) hN)).det.val : ℝ)
      = (N : ℝ) ^ 2 := by
    rw [GeneralLinearGroup.det_scalar]
    simp [Fintype.card_fin]
  have hpos : 0 < ((GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (N : ℝ) hN)).det.val : ℝ) := by
    rw [hdet]
    exact pow_two_pos_of_ne_zero hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hN : N ≠ 0)
  have hσ : UpperHalfPlane.σ (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (N : ℝ) hN))
      = .refl ℝ ℂ := by
    simp only [UpperHalfPlane.σ, hpos, ↓reduceIte]
  rw [slash_apply, hσ, hdet,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar,
    abs_of_nonneg (sq_nonneg (N : ℝ))]
  simp only [ContinuousAlgEquiv.refl_apply, Units.val_mk0, Complex.ofReal_pow,
    Complex.ofReal_natCast, Pi.smul_apply, smul_eq_mul]
  have key : ((N : ℂ) ^ 2) ^ (k - 1) * (N : ℂ) ^ (-k) = (N : ℂ) ^ (k - 2) := by
    rw [← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ hNc]
    congr 1
    push_cast
    ring
  rw [mul_assoc, key, mul_comm]

variable (N : ℕ) [NeZero N]

/-- For `N ≠ 0` (`[NeZero N]`), the Fricke matrix `W_N = !![0, -1; N, 0]` as an element of
`GL (Fin 2) ℝ`. -/
def frickeGL : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℝ), 0] (by
    rw [det_fin_two_of]
    simpa using (NeZero.ne N))

@[simp] theorem val_frickeGL :
    ((frickeGL N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (N : ℝ), 0] :=
  rfl

theorem det_frickeGL : ((frickeGL N).det : ℝ) = N := by
  rw [GeneralLinearGroup.val_det_apply, val_frickeGL, det_fin_two_of]
  ring

/-- For `N ≠ 0` (`[NeZero N]`), the square of the Fricke matrix `W_N` is the scalar matrix
`-N`. -/
theorem frickeGL_mul_frickeGL :
    frickeGL N * frickeGL N
      = -GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (N : ℝ) (by exact_mod_cast NeZero.ne N)) := by
  apply Units.ext
  rw [Units.val_mul, val_frickeGL, Units.val_neg,
    show ((GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (N : ℝ) (by exact_mod_cast NeZero.ne N)) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) (N : ℝ) from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.natCast_apply]

/-- For `N ≠ 0` (`[NeZero N]`), slashing a function `f : ℍ → ℂ` twice in weight `k` by the
Fricke matrix `W_N` multiplies it by `(-1) ^ k * N ^ (k - 2)`. -/
theorem slash_frickeGL_slash_frickeGL (k : ℤ) (f : ℍ → ℂ) :
    (f ∣[k] frickeGL N) ∣[k] frickeGL N = ((-1 : ℂ) ^ k * (N : ℂ) ^ (k - 2)) • f := by
  rw [← SlashAction.slash_mul, frickeGL_mul_frickeGL, slash_neg, slash_scalar_natCast]
  ext τ
  simp [mul_assoc]

/-- The Fricke matrix as a rational matrix. -/
private def frickeGLQ : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℚ), 0] (by
    rw [det_fin_two_of]
    simpa using (NeZero.ne N))

private theorem frickeGLQ_map : (frickeGLQ N).map (Rat.castHom ℝ) = frickeGL N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeGLQ, GeneralLinearGroup.mkOfDetNeZero]

/-- For `N ≠ 0` (`[NeZero N]`), the Fricke matrix `W_N` normalizes `Γ₀(N)`: for every
`γ ∈ Γ₀(N)` there is `γ' ∈ Γ₀(N)` with `W_N γ = γ' W_N` in `GL (Fin 2) ℝ`. -/
theorem exists_frickeGL_mul_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ γ' ∈ Gamma0 N, frickeGL N * SpecialLinearGroup.mapGL ℝ γ
      = SpecialLinearGroup.mapGL ℝ γ' * frickeGL N := by
  have hc : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp hγ)
  obtain ⟨c, hc⟩ := hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.2
    rwa [det_fin_two] at h
  let γ' : SL(2, ℤ) := ⟨!![γ 1 1, -c; -(N : ℤ) * γ 0 1, γ 0 0], by
    rw [det_fin_two_of]
    rw [hc] at hdet
    linear_combination hdet⟩
  refine ⟨γ', ?_, ?_⟩
  · rw [Gamma0_mem]
    simp [γ']
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, val_frickeGL,
      show ((SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) from rfl,
      show ((SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) from rfl]
    have h10 : (γ 1 0 : ℝ) = (N : ℝ) * c := by exact_mod_cast hc
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ', Matrix.mul_apply, Fin.sum_univ_two, h10] <;> ring

/-- For `N ≠ 0` (`[NeZero N]`) and a modular form `f` of weight `k` on `Γ₀(N)`, the function
`f ∣[k] W_N` is again invariant under the weight-`k` slash action of `Γ₀(N)`. -/
theorem slash_frickeGL_slash_eq_self {k : ℤ} (f : ModularForm (Gamma0 N) k) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (⇑f ∣[k] frickeGL N) ∣[k] γ = ⇑f ∣[k] frickeGL N := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨γ', hγ', heq⟩ := exists_frickeGL_mul_eq N hγ₀
  rw [← SlashAction.slash_mul, heq, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ')]

/-- For `N ≠ 0` (`[NeZero N]`), the Fricke operator `f ↦ f ∣[k] W_N`, a `ℂ`-linear map from
the modular forms of weight `k` on `Γ₀(N)` to themselves. -/
def fricke (k : ℤ) : ModularForm (Gamma0 N) k →ₗ[ℂ] ModularForm (Gamma0 N) k where
  toFun f :=
    { toFun := ⇑f ∣[k] frickeGL N
      slash_action_eq' := fun _ hγ => slash_frickeGL_slash_eq_self N f hγ
      holo' := (ModularFormClass.holo f).slash k (frickeGL N)
      bdd_at_cusps' := fun {c} hc => by
        rw [← frickeGLQ_map, ← OnePoint.IsBoundedAt.smul_iff]
        refine ModularFormClass.bdd_at_cusps f ?_
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
        obtain ⟨c, rfl⟩ := hc
        exact ⟨frickeGLQ N • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩ }
  map_add' f g := by
    ext τ
    change ((⇑f + ⇑g) ∣[k] frickeGL N) τ = (⇑f ∣[k] frickeGL N) τ + (⇑g ∣[k] frickeGL N) τ
    rw [SlashAction.add_slash]
    rfl
  map_smul' c f := by
    ext τ
    have hpos : 0 < ((frickeGL N).det : ℝ) := by
      rw [det_frickeGL]
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hσ : UpperHalfPlane.σ (frickeGL N) = .refl ℝ ℂ := by
      simp only [UpperHalfPlane.σ, hpos, ↓reduceIte]
    change ((c • ⇑f) ∣[k] frickeGL N) τ = c * (⇑f ∣[k] frickeGL N) τ
    rw [smul_slash, hσ]
    rfl

theorem coe_fricke (k : ℤ) (f : ModularForm (Gamma0 N) k) :
    ⇑(fricke N k f) = ⇑f ∣[k] frickeGL N :=
  rfl

/-- For `N ≠ 0` (`[NeZero N]`) and a modular form `f` of weight `k` on `Γ₀(N)`, slashing the
Fricke transform of `f` once more by `W_N` gives `(-1) ^ k * N ^ (k - 2)` times `f`. -/
theorem coe_fricke_slash_frickeGL (k : ℤ) (f : ModularForm (Gamma0 N) k) :
    ⇑(fricke N k f) ∣[k] frickeGL N = ((-1 : ℂ) ^ k * (N : ℂ) ^ (k - 2)) • ⇑f :=
  slash_frickeGL_slash_frickeGL N k f

end ModularForm
