/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularForm_HeckeOperator.lean`,
`Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean`,
`Definitions/Def_FreyPackage_ModMCarrier_OldSublattice.lean`,
`Theorems/Thm_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin.lean` and
`P2M/Sol/S_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed, the names restated in Mathlib style, and the proofs rewritten to use
Mathlib's `CuspForm` / `ModularForm` API directly.
-/

module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularForm

/-- The diagonal matrix `!![d, 0; 0, 1]` in `GL (Fin 2) ℝ`, with the
convention that it is the identity when `d = 0`. Slashing by this matrix
rescales the argument of a function on the upper half-plane. -/
noncomputable def heckeDiagMatrix (d : ℕ) : GL (Fin 2) ℝ :=
  if hp : d = 0 then 1
  else
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℝ), 0; 0, 1]
      (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hp)

@[simp] lemma val_heckeDiagMatrix {d : ℕ} (hd : d ≠ 0) :
    ((heckeDiagMatrix d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(d : ℝ), 0; 0, 1] := by
  simp [heckeDiagMatrix, hd]

@[simp] lemma heckeDiagMatrix_zero : heckeDiagMatrix 0 = 1 := by
  simp [heckeDiagMatrix]

/-- Rescaling by `1` is the identity matrix. -/
lemma heckeDiagMatrix_one : heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The determinant of the diagonal rescaling matrix is positive. -/
lemma det_heckeDiagMatrix_pos (d : ℕ) : 0 < ((heckeDiagMatrix d).det : ℝ) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeDiagMatrix hd,
      Matrix.det_fin_two_of]
    simp; exact_mod_cast Nat.pos_of_ne_zero hd

/-- The diagonal rescaling matrix has trivial `σ`-factor. -/
lemma σ_heckeDiagMatrix (d : ℕ) :
    UpperHalfPlane.σ (heckeDiagMatrix d) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, ite_eq_left (det_heckeDiagMatrix_pos d)]

/-- The determinant of the diagonal rescaling matrix is the rescaling
factor. -/
lemma det_heckeDiagMatrix {d : ℕ} (hd : d ≠ 0) :
    ((heckeDiagMatrix d).det : ℝ) = (d : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeDiagMatrix hd,
    Matrix.det_fin_two_of]
  simp

/-- The denominator of the diagonal rescaling matrix is `1`. -/
lemma denom_heckeDiagMatrix {d : ℕ} (hd : d ≠ 0) (τ : ℍ) :
    UpperHalfPlane.denom (heckeDiagMatrix d) τ = 1 := by
  simp [UpperHalfPlane.denom, val_heckeDiagMatrix hd]

/-- The diagonal rescaling matrix sends `τ` to `d • τ` on the upper
half-plane. -/
lemma coe_heckeDiagMatrix_smul {d : ℕ} (hd : d ≠ 0) (τ : ℍ) :
    ((heckeDiagMatrix d • τ : ℍ) : ℂ) = (d : ℂ) * (τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeDiagMatrix_pos d)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeDiagMatrix hd]

/-- Slash action by the diagonal rescaling matrix: it rescales the
argument and multiplies by the `(k - 1)`-st power of the factor. -/
lemma slash_heckeDiagMatrix_apply (k : ℤ) {d : ℕ} (hd : d ≠ 0) (f : ℍ → ℂ)
    (τ : ℍ) :
    (f ∣[k] heckeDiagMatrix d) τ = (d : ℂ) ^ (k - 1) * f (heckeDiagMatrix d • τ) := by
  rw [ModularForm.slash_apply, σ_heckeDiagMatrix, det_heckeDiagMatrix hd,
    denom_heckeDiagMatrix hd]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast,
    one_zpow, mul_one]
  rw [mul_comm]

end ModularForm

namespace CuspForm

open ModularForm

variable {R M d : ℕ}

private lemma aux_neZero_d [NeZero M] (hdRM : d * R ∣ M) : d ≠ 0 := by
  rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (zero_mul R ▸ hdRM))

private lemma aux_neZero_R [NeZero M] (hdRM : d * R ∣ M) : NeZero R :=
  ⟨by rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (mul_zero d ▸ hdRM))⟩


/-- If `d * R ∣ M` and `γ ∈ Γ₀(M)`, then `diag(d, 1) * γ = δ * diag(d, 1)` as integer
matrices for some `δ ∈ Γ₀(R)`. For `d ≠ 0`, `diag(d, 1)` is invertible over `ℚ` and
`δ = diag(d, 1) * γ * diag(d, 1)⁻¹`, so conjugation by `diag(d, 1)` carries `Γ₀(M)` into
`Γ₀(R)`. -/
lemma exists_cocycle_rescale (hdRM : d * R ∣ M) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 R ∧
      !![(d : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![(d : ℤ), 0; 0, 1] := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := γ.det_coe; rwa [Matrix.det_fin_two] at h
  have hMc : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := Gamma0_mem.mp hγ; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set e : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with he
  have hγmat : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, e] := by
    rw [ha, hb, hc, he]; exact Matrix.eta_fin_two _
  have hdRMc : ((d * R : ℕ) : ℤ) ∣ c := dvd_trans (by exact_mod_cast hdRM) hMc
  obtain ⟨c', hc'⟩ := hdRMc
  rw [Nat.cast_mul] at hc'
  have hdetδ : Matrix.det !![a, (d : ℤ) * b; (R : ℤ) * c', e] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + b * hc'
  refine ⟨(⟨_, hdetδ⟩ : SL(2, ℤ)), Gamma0_mem.mpr ?_, ?_⟩
  · show (((R : ℤ) * c' : ℤ) : ZMod R) = 0
    simp
  · show !![(d : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)
      = !![a, (d : ℤ) * b; (R : ℤ) * c', e] * !![(d : ℤ), 0; 0, 1]
    rw [hγmat]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show ((d : ℤ) * a + 0 * c : ℤ) = a * (d : ℤ) + (d : ℤ) * b * 0; ring
    · show ((d : ℤ) * b + 0 * e : ℤ) = a * 0 + (d : ℤ) * b * 1; ring
    · show (0 * a + 1 * c : ℤ) = (R : ℤ) * c' * (d : ℤ) + e * 0; linear_combination hc'
    · show (0 * b + 1 * e : ℤ) = (R : ℤ) * c' * 0 + e * 1; ring

private lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul_eq (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * B.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    map_mul]

private lemma diagMat_map_eq (hd : d ≠ 0) :
    (!![(d : ℤ), 0; 0, 1]).map (algebraMap ℤ ℝ)
      = ((heckeDiagMatrix d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeDiagMatrix hd]
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma rescaleSlash_slash [NeZero M] (hdRM : d * R ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (f ∣[k] heckeDiagMatrix d) ∣[k] γ = f ∣[k] heckeDiagMatrix d := by
  have hd : d ≠ 0 := aux_neZero_d hdRM
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨δ, hδ, hconj⟩ := exists_cocycle_rescale hdRM hg
  have hGL : heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ g
      = Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeDiagMatrix d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (heckeDiagMatrix d : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (heckeDiagMatrix d : Matrix (Fin 2) (Fin 2) ℝ)
    rw [← diagMat_map_eq hd, mapGL_coe_eq, mapGL_coe_eq, ← map_int_mul_eq,
      ← map_int_mul_eq, hconj]
  calc (f ∣[k] heckeDiagMatrix d) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ g
      = f ∣[k] (heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ g) :=
        (SlashAction.slash_mul k _ _ f).symm
    _ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeDiagMatrix d) := by
        rw [hGL]
    _ = (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ δ) ∣[k] heckeDiagMatrix d :=
        SlashAction.slash_mul k _ _ f
    _ = f ∣[k] heckeDiagMatrix d := by
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ δ)
          (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]

/-- The rational diagonal matrix `!![d, 0; 0, 1]` in `GL (Fin 2) ℚ`. -/
def heckeDiagMatrixQ (hd : d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hd)

private lemma heckeDiagMatrixQ_map (hd : d ≠ 0) :
    (heckeDiagMatrixQ hd).map (Rat.castHom ℝ) = heckeDiagMatrix d := by
  apply Units.ext
  rw [val_heckeDiagMatrix hd]
  show (heckeDiagMatrixQ hd : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold heckeDiagMatrixQ
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ)
    {g : GL (Fin 2) ℝ} (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) :
    IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

lemma rescaleSlash_isZeroAt [NeZero M] [NeZero R] (hd : d ≠ 0) (k : ℤ)
    {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (f ∣[k] heckeDiagMatrix d) k := by
  refine OnePoint.IsZeroAt.smul_iff.mp (hf _ ?_)
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_of_rat hc (heckeDiagMatrixQ hd) (heckeDiagMatrixQ_map hd)

/-- Rescaling a cusp form: for `d * R ∣ M`, the map sending a cusp form
`f` of level `Γ₀(R)` and weight `k` to the cusp form of level `Γ₀(M)`
whose underlying function is `f` slashed by the diagonal matrix
`!![d, 0; 0, 1]`. On the upper half-plane this is, up to the usual
slash-action factor, the substitution `τ ↦ d • τ`. -/
noncomputable def rescaleLin [NeZero M] (hdRM : d * R ∣ M) (k : ℤ) :
    CuspForm (Gamma0 R) k →ₗ[ℂ] CuspForm (Gamma0 M) k where
  toFun f :=
    haveI : NeZero R := ⟨by
      rintro rfl
      exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (mul_zero d ▸ hdRM))⟩
    { toSlashInvariantForm :=
        { toFun := ⇑f ∣[k] heckeDiagMatrix d
          slash_action_eq' := fun γ hγ => rescaleSlash_slash hdRM k
            (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) hγ }
      holo' := (CuspFormClass.holo f).slash k (heckeDiagMatrix d)
      zero_at_cusps' := fun {c} hc => rescaleSlash_isZeroAt (by
          rintro rfl
          exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (zero_mul R ▸ hdRM))) k
        (fun c' hc' => CuspFormClass.zero_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <| by
    show (⇑(f + g)) ∣[k] heckeDiagMatrix d
      = (⇑f ∣[k] heckeDiagMatrix d) + (⇑g ∣[k] heckeDiagMatrix d)
    rw [FunLike.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show (⇑(c • f)) ∣[k] heckeDiagMatrix d = c • (⇑f ∣[k] heckeDiagMatrix d)
    rw [FunLike.coe_smul, ModularForm.smul_slash, σ_heckeDiagMatrix]
    simp

@[simp] lemma coe_rescaleLin_apply [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) :
    ⇑(rescaleLin hdRM k f) = ⇑f ∣[k] heckeDiagMatrix d := rfl

/-- Level inclusion for `Γ₀`: if `R ∣ M` then `Γ₀(M) ≤ Γ₀(R)` as
subgroups of `SL(2, ℤ)`. -/
lemma Gamma0_le_Gamma0_of_dvd {R M : ℕ} (hRM : R ∣ M) :
    Gamma0 M ≤ Gamma0 R := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have hcast : ZMod.castHom hRM (ZMod R) (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M)
      = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod R) := map_intCast _ _
  rw [← hcast, hγ, map_zero]

/-- Level inclusion for cusp forms: for `R ∣ M`, a cusp form of level
`Γ₀(R)` and weight `k` is also a cusp form of level `Γ₀(M)`, with the
same underlying function. -/
noncomputable def levelInclusionLin [NeZero M] (hRM : R ∣ M) (k : ℤ) :
    CuspForm (Gamma0 R) k →ₗ[ℂ] CuspForm (Gamma0 M) k where
  toFun f :=
    { toSlashInvariantForm :=
        { toFun := ⇑f
          slash_action_eq' := fun γ hγ =>
            f.slash_action_eq' γ (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd hRM) hγ) }
      holo' := f.holo'
      zero_at_cusps' := fun {c} hc =>
        f.zero_at_cusps' (hc.mono (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd hRM))) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coe_levelInclusionLin_apply [NeZero M] (hRM : R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) : ⇑(levelInclusionLin hRM k f) = ⇑f := rfl

/-- Rescaling by `1` agrees with level inclusion: for `R ∣ M`, the
rescaled form `f(dτ)` at `d = 1` is the same cusp form of level
`Γ₀(M)` as the one obtained by viewing `f` at the higher level. -/
public theorem rescaleLin_eq_levelInclusionLin {R M : ℕ} [NeZero M]
    (h : 1 * R ∣ M) (hRM : R ∣ M) (k : ℤ) (f : CuspForm (Gamma0 R) k) :
    rescaleLin h k f = levelInclusionLin hRM k f := by
  refine DFunLike.coe_injective ?_
  change ⇑(rescaleLin h k f) = ⇑(levelInclusionLin hRM k f)
  rw [coe_rescaleLin_apply, coe_levelInclusionLin_apply, heckeDiagMatrix_one,
    SlashAction.slash_one]

end CuspForm
