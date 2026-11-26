/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.AdelicLift

@[expose] public section

open NumberField

open scoped ModularForm

/-- The zero function is an adelic lift of the zero cusp form at every level, so the three
clauses of `IsAdelicLiftOf` can hold together. -/
example {M : ℕ} :
    CuspForm.IsAdelicLiftOf (0 : CuspForm (CongruenceSubgroup.Gamma0 M) 2) 0 :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => by simp⟩

/-- The third clause at the identity: a lift takes the value `g I` at `1`. -/
private theorem lift_apply_one {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : CuspForm.IsAdelicLiftOf g φ) :
    φ 1 = g UpperHalfPlane.I := by
  have h1 : LanglandsTunnell.ratArchGL2 1 = 1 := by
    unfold LanglandsTunnell.ratArchGL2
    rw [map_one, map_one, map_one]
  rw [hφ.apply_eq 1 (map_one _) (by rw [h1]; exact one_mem _), h1, SlashAction.slash_one]

/-- With left invariance, a lift takes the value `g I` at every rational point. -/
example {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : CuspForm.IsAdelicLiftOf g φ)
    (γ : GL (Fin 2) ℚ) :
    φ (NumberField.globalPoints (𝓞 ℚ) ℚ γ) = g UpperHalfPlane.I := by
  rw [← mul_one (NumberField.globalPoints (𝓞 ℚ) ℚ γ), hφ.left_inv γ 1, lift_apply_one hφ]

/-- With right invariance, a lift takes the value `g I` on the embedded finite level
subgroup. -/
example {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : CuspForm.IsAdelicLiftOf g φ)
    {u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ
      (NumberField.AdelicLevel.ratLevel M)) :
    φ (NumberField.AdelicLevel.finEmbed (𝓞 ℚ) ℚ u) = g UpperHalfPlane.I := by
  rw [← one_mul (NumberField.AdelicLevel.finEmbed (𝓞 ℚ) ℚ u), hφ.level_inv u hu 1,
    lift_apply_one hφ]

/-- The adelic element with archimedean part the rational matrix `γ` and finite part `1`. -/
private noncomputable def archPoint (γ : GL (Fin 2) ℚ) : NumberField.AdelicGL2 (𝓞 ℚ) ℚ :=
  (Matrix.GeneralLinearGroup.prodEquiv (Fin 2) (InfiniteAdeleRing ℚ)
    (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)).symm
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ)) γ, 1)

private theorem glFin_archPoint (γ : GL (Fin 2) ℚ) :
    NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ (archPoint γ) = 1 :=
  congrArg Prod.snd ((Matrix.GeneralLinearGroup.prodEquiv (Fin 2) (InfiniteAdeleRing ℚ)
    (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)).apply_symm_apply
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ)) γ, 1))

private theorem ratArchGL2_archPoint (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPoint γ) =
      Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact congrArg (fun f : ℚ →+* ℝ => f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j))
    (RingHom.ext_rat ((InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).toRingHom.comp
        ((NumberField.AdelicLevel.archEval ℚ default).comp
          (algebraMap ℚ (InfiniteAdeleRing ℚ)))) (Rat.castHom ℝ))

private theorem mem_glpos_map_iff (γ : GL (Fin 2) ℚ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ ∈ Matrix.GLPos (Fin 2) ℝ ↔
      0 < (γ : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_ofClass,
    Matrix.GeneralLinearGroup.val_det_apply, eq_ratCast, Rat.cast_pos]

/-- The third clause away from the identity: at the element with archimedean part a rational
matrix `γ` of positive determinant and finite part `1`, a lift takes the value
`(g ∣[2] γ) I`. -/
example {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : CuspForm.IsAdelicLiftOf g φ)
    (γ : GL (Fin 2) ℚ) (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℚ).det) :
    φ (archPoint γ) =
      ((⇑g) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ) UpperHalfPlane.I := by
  rw [hφ.apply_eq _ (glFin_archPoint γ)
    (by rw [ratArchGL2_archPoint, mem_glpos_map_iff]; exact hγ), ratArchGL2_archPoint]

/-- The positive-determinant hypothesis of the third clause is not vacuous: the archimedean
point of `diag(-1, 1)` has trivial finite part, but its real matrix is not in `GLPos`. -/
example : LanglandsTunnell.ratArchGL2
      (archPoint (Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1]
        (by simp [Matrix.det_fin_two]))) ∉ Matrix.GLPos (Fin 2) ℝ := by
  rw [ratArchGL2_archPoint, mem_glpos_map_iff]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]

/-- `finEmbed u` has entries `(1 i j, u i j)`: archimedean part `1`, finite part `u`. -/
example (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 2) :
    ((NumberField.AdelicLevel.finEmbed (𝓞 ℚ) ℚ u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
        (u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :=
  rfl

/-- `ratArchGL2` is trivial on elements with archimedean part `1`. -/
example (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (NumberField.AdelicLevel.finEmbed (𝓞 ℚ) ℚ u) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [NumberField.AdelicLevel.glArch_finEmbed, map_one, map_one]

/-- On rational points, `ratArchGL2` is the rational matrix read in `ℝ`. -/
example (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (NumberField.globalPoints (𝓞 ℚ) ℚ γ) =
      Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact congrArg (fun f : ℚ →+* ℝ => f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j))
    (RingHom.ext_rat ((InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).toRingHom.comp
        ((NumberField.AdelicLevel.archEval ℚ default).comp
          ((NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).comp
            (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))) (Rat.castHom ℝ))

/-- At level `0` the level ideal is `⊥`, so `ratLevel_ne_bot` needs its hypothesis `N ≠ 0`. -/
example : NumberField.AdelicLevel.ratLevel 0 = ⊥ :=
  Ideal.span_singleton_eq_bot.mpr Nat.cast_zero

/-- At level `1` the level ideal is the whole ring. -/
example : NumberField.AdelicLevel.ratLevel 1 = ⊤ :=
  NumberField.AdelicLevel.ratLevel_one

/-- At every nonzero level the level ideal is nonzero. -/
example {N : ℕ} (hN : N ≠ 0) : NumberField.AdelicLevel.ratLevel N ≠ ⊥ :=
  NumberField.AdelicLevel.ratLevel_ne_bot hN
