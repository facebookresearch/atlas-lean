/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicHeight

@[expose] public section

open NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain

/-- The height of the identity is `1`. -/
example : adelicHeight ℚ 1 = 1 := adelicHeight_one ℚ

/-- The criterion applied to the identity map and the identity permutations of places. -/
example (F : Type*) [Field F] [NumberField F] (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    adelicHeight F (Matrix.GeneralLinearGroup.map (RingHom.id _) g) = adelicHeight F g :=
  adelicHeight_map_of_norm_eq (RingHom.id _) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) g

/-- The finite local height of a scalar matrix `c • 1` is `1`, whatever `c ≠ 0` is: the
determinant `c²` cancels the bottom row `(0, c)`. -/
example (c : ℚ) (hc : c ≠ 0) :
    finLocalHeight (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun _ => c)
      (by simpa [Matrix.det_diagonal] using pow_ne_zero 2 hc)) = 1 := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  simp [finLocalHeight, rowMaxNorm, Matrix.det_fin_two, Matrix.diagonal]
  field_simp

section Archimedean

/-- The real matrix with rows `(1, 0)` and `(1, 1)`, of determinant `1`. -/
private noncomputable def lowerOne : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])

/-- Its archimedean local height is `1 / 2`: the determinant `1` over the sum of squares `1 + 1`
of the bottom row. -/
example : archLocalHeight lowerOne = 1 / 2 := by
  simp [archLocalHeight, rowNormSq, lowerOne, Matrix.det_fin_two]
  norm_num

/-- Its finite local height, with the maximum `1` of the bottom row in place of the sum of
squares, is `1`. -/
example : finLocalHeight lowerOne = 1 := by
  simp [finLocalHeight, rowMaxNorm, lowerOne, Matrix.det_fin_two]

/-- With bottom row `(2, 1)` the sum of squares is `5`, so the archimedean local height is
`1 / 5`, against `1 / 3` for the sum of the norms and `1 / 4` for the maximum squared. -/
example : archLocalHeight (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 2, 1]
    (by simp [Matrix.det_fin_two])) = 1 / 5 := by
  simp [archLocalHeight, rowNormSq, Matrix.det_fin_two]
  norm_num

/-- The same matrix over `ℚ`. -/
private noncomputable def lowerOneRat : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])

/-- Over `ℚ`, whose only infinite place is real (multiplicity `1`), the archimedean height of
that matrix in `GL₂` of the infinite adeles is `1 / 2`. -/
private theorem archHeight_lowerOneRat :
    archHeight ℚ (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ))
      lowerOneRat) = 1 / 2 := by
  have hm : (default : InfinitePlace ℚ).mult = 1 :=
    InfinitePlace.mult_isReal ⟨_, Rat.isReal_infinitePlace⟩
  rw [archHeight, Fintype.prod_unique, hm, pow_one]
  simp [archLocalHeight, rowNormSq, lowerOneRat, Matrix.det_fin_two, archComponent_apply,
    Matrix.GeneralLinearGroup.map_apply]
  norm_num

/-- The adelic height sees the archimedean part: the adele with archimedean part that matrix and
finite part `1` has adelic height `1 / 2`. -/
example : adelicHeight ℚ ((Matrix.GeneralLinearGroup.prodEquiv (Fin 2) (InfiniteAdeleRing ℚ)
    (FiniteAdeleRing (𝓞 ℚ) ℚ)).symm
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ)) lowerOneRat, 1)) =
    1 / 2 := by
  have e := (Matrix.GeneralLinearGroup.prodEquiv (Fin 2) (InfiniteAdeleRing ℚ)
    (FiniteAdeleRing (𝓞 ℚ) ℚ)).apply_symm_apply
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ)) lowerOneRat, 1)
  have harch : glArch (𝓞 ℚ) ℚ ((Matrix.GeneralLinearGroup.prodEquiv (Fin 2)
      (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).symm
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ)) lowerOneRat, 1)) =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ)) lowerOneRat :=
    congrArg Prod.fst e
  have hfin : glFin (𝓞 ℚ) ℚ ((Matrix.GeneralLinearGroup.prodEquiv (Fin 2)
      (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).symm
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ)) lowerOneRat, 1)) =
      1 :=
    congrArg Prod.snd e
  have h1 : finHeight ℚ 1 = 1 := by simp [finHeight, finLocalHeight_one]
  rw [adelicHeight, harch, hfin, h1, mul_one]
  exact archHeight_lowerOneRat

end Archimedean

section FinitePlace

variable {F : Type*} [Field F] [NumberField F]

/-- `diag(x, 1)` over the finite adeles of `F`, for `x ≠ 0` in `F`. -/
private noncomputable def diagFin (x : F) (hx : x ≠ 0) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.GeneralLinearGroup.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![x, 0; 0, 1] (by simp [Matrix.det_fin_two, hx]))

/-- At every finite place `w`, the local height of `diag(x, 1)` is `‖x‖_w`. -/
private theorem finLocalHeight_diagFin (x : F) (hx : x ≠ 0) (w : HeightOneSpectrum (𝓞 F)) :
    finLocalHeight (finComponent (𝓞 F) F w (diagFin x hx)) = ‖(x : w.adicCompletion F)‖ := by
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) w = 0 := rfl
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) w = 1 := rfl
  simp [finLocalHeight, rowMaxNorm, Matrix.det_fin_two, finComponent_apply, diagFin,
    Matrix.GeneralLinearGroup.map_apply, h0, h1]

private theorem norm_coe_le_one (r : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) :
    ‖((r : F) : w.adicCompletion F)‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact HeightOneSpectrum.valuation_le_one w r

private theorem norm_coe_lt_one (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (hrv : r ∈ v.asIdeal) :
    ‖((r : F) : v.adicCompletion F)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v r).mpr hrv

/-- A finite local factor that is not `1`: for a nonzero `r` in the prime of a finite place `v`,
the local height of `diag(r, 1)` at `v` is `‖r‖_v < 1`. The finite height of `diag(r, 1)` is a
finite product by `hasFiniteMulSupport_finLocalHeight`, its other factors are at most `1`, so it
is `< 1` as well. -/
private theorem finHeight_diagFin_lt_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F)
    (hr : (r : F) ≠ 0) (hrv : r ∈ v.asIdeal) :
    finLocalHeight (finComponent (𝓞 F) F v (diagFin (r : F) hr)) < 1 ∧
      finHeight F (diagFin (r : F) hr) < 1 := by
  classical
  have hv : finLocalHeight (finComponent (𝓞 F) F v (diagFin (r : F) hr)) < 1 := by
    rw [finLocalHeight_diagFin]
    exact norm_coe_lt_one r v hrv
  refine ⟨hv, ?_⟩
  have hfin := hasFiniteMulSupport_finLocalHeight (diagFin (r : F) hr)
  have hmem : v ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr hv.ne
  rw [finHeight, finprod_eq_prod _ hfin, ← Finset.mul_prod_erase _ _ hmem]
  refine lt_of_le_of_lt ?_ hv
  refine mul_le_of_le_one_right (by rw [finLocalHeight_diagFin]; exact norm_nonneg _) ?_
  refine Finset.prod_le_one₀ (fun w _ => ?_) (fun w _ => ?_)
  · rw [finLocalHeight_diagFin]
    exact norm_nonneg _
  · rw [finLocalHeight_diagFin]
    exact norm_coe_le_one r w

/-- Every finite place `v` has such an element, so the finite height is not identically `1`. -/
example (v : HeightOneSpectrum (𝓞 F)) : ∃ g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F),
    finLocalHeight (finComponent (𝓞 F) F v g) < 1 ∧ finHeight F g < 1 := by
  obtain ⟨r, hrv, hr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  exact ⟨_, finHeight_diagFin_lt_one v r (RingOfIntegers.coe_ne_zero_iff.mpr hr) hrv⟩

/-- The adelic height sees the finite part: the adele with archimedean part `1` and finite part
`diag(r, 1)` has adelic height `finHeight F (diag(r, 1)) < 1`. -/
example (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : (r : F) ≠ 0) (hrv : r ∈ v.asIdeal) :
    adelicHeight F ((Matrix.GeneralLinearGroup.prodEquiv (Fin 2) (InfiniteAdeleRing F)
      (FiniteAdeleRing (𝓞 F) F)).symm (1, diagFin (r : F) hr)) < 1 := by
  have e := (Matrix.GeneralLinearGroup.prodEquiv (Fin 2) (InfiniteAdeleRing F)
    (FiniteAdeleRing (𝓞 F) F)).apply_symm_apply (1, diagFin (r : F) hr)
  have harch : glArch (𝓞 F) F ((Matrix.GeneralLinearGroup.prodEquiv (Fin 2)
      (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).symm (1, diagFin (r : F) hr)) = 1 :=
    congrArg Prod.fst e
  have hfin : glFin (𝓞 F) F ((Matrix.GeneralLinearGroup.prodEquiv (Fin 2)
      (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).symm (1, diagFin (r : F) hr)) =
      diagFin (r : F) hr :=
    congrArg Prod.snd e
  have h1 : archHeight F 1 = 1 := by simp [archHeight, archLocalHeight_one]
  rw [adelicHeight, harch, hfin, h1, one_mul]
  exact (finHeight_diagFin_lt_one v r hr hrv).2

end FinitePlace
