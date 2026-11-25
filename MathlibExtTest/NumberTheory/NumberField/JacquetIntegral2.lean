/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_LanglandsTunnell_CubicInduction_absoluteJacquetIntegral_lt_top_
and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.NumberTheory.NumberField.JacquetIntegral2

@[expose] public section

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction AutomorphicForm
open scoped NNReal ENNReal

/-- `exactSource` consumer with the original binders, including the Borel σ-algebra fixed
inside the conclusion. -/
example
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (hfsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := borel _
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν < ∞) ∧
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ∫⁻ y, ‖f (w₀ * unipotentGL2 y * (unipotentGL2 x * g))‖ₑ ∂ν =
          ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν) ∧
      (∀ (t₁ t₂ : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ∫⁻ y, ‖f (w₀ * unipotentGL2 y * (diagonal2 p ![t₁, t₂] * g))‖ₑ ∂ν =
          ENNReal.ofReal (‖((χ 0 t₂ : ℂˣ) : ℂ)‖ * ‖((χ 1 t₁ : ℂˣ) : ℂ)‖ *
              Real.sqrt (‖(t₁ : p.adicCompletion ℚ)‖ / ‖(t₂ : p.adicCompletion ℚ)‖)) *
            ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν) ∧
      (∃ C : ℝ≥0, ∀ k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ∫⁻ y, ‖f (w₀ * unipotentGL2 y * k)‖ₑ ∂ν ≤ C) :=
  letI : MeasurableSpace (p.adicCompletion ℚ) := borel _
  haveI : BorelSpace (p.adicCompletion ℚ) := ⟨rfl⟩
  absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
    p χ cχ hcχ ϖ hϖ hdom f hf hfsm w₀ hw₀

/-- Boundary check: the identity lies in the local level-one subgroup, so the bound in the last
conjunct is a genuine constraint on a nonempty set. -/
example (p : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤ :=
  Subgroup.one_mem _

namespace JacquetIntegral2Test

variable (p : HeightOneSpectrum (𝓞 ℚ))

/-- The character `u ↦ ‖u‖⁻¹` of `ℚ_pˣ`. -/
private noncomputable def normInvChar : (p.adicCompletion ℚ)ˣ →* ℂˣ where
  toFun u := Units.mk0 ((‖(u : p.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr u.ne_zero)))
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp; ring)

/-- The pair of characters `(1, ‖·‖⁻¹)`. -/
private noncomputable abbrev chi : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ) :=
  ![1, normInvChar p]

/-- The spherical vector of `principalSeries2 p (chi p)`:
`g ↦ √‖det g‖ / max ‖g₁₀‖ ‖g₁₁‖ ^ 2`. -/
private noncomputable def sph (g : GL (Fin 2) (p.adicCompletion ℚ)) : ℂ :=
  ((Real.sqrt ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
    max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
      ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ)

/-- The Weyl element `!![0, 1; 1, 0]`. -/
private noncomputable def weyl : GL (Fin 2) (p.adicCompletion ℚ) where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem idealBound_top : AdelicLevel.idealBound (𝓞 ℚ) ⊤ p = 1 := by
  rw [AdelicLevel.idealBound, ite_eq_right_iff.mpr fun h => absurd h top_ne_bot,
    ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero p.associates_irreducible]
  rfl

private theorem norm_le_one_of_mem {x : p.adicCompletion ℚ}
    (hx : x ∈ p.adicCompletionIntegers ℚ) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx)

/-- At the full ideal the local level-one subgroup is `GL₂` of the integers. -/
private theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (p.adicCompletion ℚ)) :
    k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤ ↔
      (∀ i j, (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈
        p.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ := by
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
      (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) → AdelicLevel.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m :=
    fun m hm => ⟨hm,
      by rw [idealBound_top]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm 1 0),
      by
        rw [idealBound_top]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
          (sub_mem (hm 1 1) (one_mem _))⟩
  rw [AdelicLevel.mem_localLevelOne_iff]
  exact ⟨fun h => ⟨h.1.integral, h.2.integral⟩, fun h => ⟨key _ h.1, key _ h.2⟩⟩

private theorem isOpen_localLevelOne_top :
    IsOpen (AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  have hO : IsOpen (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
    Valued.isOpen_valuationSubring _
  have heq : (AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      (⋂ i, ⋂ j, (fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
        (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ⁻¹'
          (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
      (⋂ i, ⋂ j, (fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
          i j) ⁻¹' (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) := by
    ext k
    simp only [SetLike.mem_coe, mem_localLevelOne_top_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage]
  rw [heq]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_val.matrix_elem i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_coe_inv.matrix_elem i j))

private theorem norm_det_eq_one {k : GL (Fin 2) (p.adicCompletion ℚ)}
    (hk : k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ = 1 := by
  obtain ⟨h1, h2⟩ := (mem_localLevelOne_top_iff p k).mp hk
  have hdet : ∀ m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
      (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) → ‖m.det‖ ≤ 1 := fun m hm => by
    rw [Matrix.det_fin_two]
    exact norm_le_one_of_mem p (sub_mem (mul_mem (hm 0 0) (hm 1 1)) (mul_mem (hm 0 1) (hm 1 0)))
  have hmul : ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ *
      ‖((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, norm_one]
  have ha := hdet _ h1
  have hb := hdet _ h2
  refine le_antisymm ha ?_
  nlinarith [norm_nonneg (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det,
    norm_nonneg ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det]

/-- Right multiplication by an integral matrix does not increase the norm of the bottom row. -/
private theorem rowMax_mul_le (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    {k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)}
    (hk : ∀ i j, k i j ∈ p.adicCompletionIntegers ℚ) :
    max ‖(g * k) 1 0‖ ‖(g * k) 1 1‖ ≤ max ‖g 1 0‖ ‖g 1 1‖ := by
  have h : ∀ j, ‖(g * k) 1 j‖ ≤ max ‖g 1 0‖ ‖g 1 1‖ := fun j => by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem p (hk 0 j))
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem p (hk 1 j))
  exact max_le (h 0) (h 1)

private theorem sph_mul_right {k : GL (Fin 2) (p.adicCompletion ℚ)}
    (hk : k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    sph p (g * k) = sph p g := by
  obtain ⟨h1, h2⟩ := (mem_localLevelOne_top_iff p k).mp hk
  have hrow : max ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
      ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ =
      max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
        ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ := by
    refine le_antisymm ?_ ?_
    · rw [Units.val_mul]
      exact rowMax_mul_le p _ h1
    · have h := rowMax_mul_le p ((g * k : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) h2
      rwa [← Units.val_mul, mul_inv_cancel_right] at h
  unfold sph
  rw [hrow, Units.val_mul, Matrix.det_mul, norm_mul, norm_det_eq_one p hk, mul_one]

private theorem sph_upper_mul (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    sph p (upperUnipotent2 p x * g) = sph p g := by
  have hrow : ∀ j, ((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j =
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j := fun j => by
    rw [Units.val_mul, upperUnipotent2_coe, Matrix.mul_apply, Fin.sum_univ_two]
    simp
  have hdet : ((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det =
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det := by
    rw [Units.val_mul, Matrix.det_mul, upperUnipotent2_coe, Matrix.det_fin_two_of]
    simp
  unfold sph
  rw [hrow, hrow, hdet]

private theorem rowMax_pos (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    0 < max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
      ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ := by
  by_contra h
  rw [not_lt] at h
  have h0 := norm_le_zero_iff.mp ((le_max_left _ _).trans h)
  have h1 := norm_le_zero_iff.mp ((le_max_right _ _).trans h)
  have hdet : (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = 0 := by
    rw [Matrix.det_fin_two, h0, h1]
    ring
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero hdet

private theorem sph_diag_mul (a : Fin 2 → (p.adicCompletion ℚ)ˣ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    sph p (diagonal2 p a * g) = torusChar2 p (chi p) a * halfModulus2 p a * sph p g := by
  have hrow : ∀ j, ((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j =
        (a 1 : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j :=
    fun j => by rw [Units.val_mul, diagonal2_coe, Matrix.diagonal_mul]
  have hdet : ((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det =
        (a 0 : p.adicCompletion ℚ) * (a 1 : p.adicCompletion ℚ) *
          (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det := by
    rw [Units.val_mul, Matrix.det_mul, diagonal2_coe, Matrix.det_diagonal, Fin.prod_univ_two]
  have htorus : torusChar2 p (chi p) a = ((‖(a 1 : p.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) := by
    simp [torusChar2, chi, normInvChar, Fin.prod_univ_two]
  have hM := rowMax_pos p g
  have h1 : 0 < ‖(a 1 : p.adicCompletion ℚ)‖ := norm_pos_iff.mpr (a 1).ne_zero
  have h0 : 0 ≤ ‖(a 0 : p.adicCompletion ℚ)‖ := norm_nonneg _
  have hD : 0 ≤ ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ := norm_nonneg _
  unfold sph halfModulus2
  rw [hrow, hrow, hdet, htorus, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [norm_mul, norm_mul, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ h1.le,
    Real.sqrt_mul (mul_nonneg h0 h1.le), Real.sqrt_mul h0, Real.sqrt_div' _ h1.le]
  have hs : Real.sqrt ‖(a 1 : p.adicCompletion ℚ)‖ ^ 2 = ‖(a 1 : p.adicCompletion ℚ)‖ :=
    Real.sq_sqrt h1.le
  have hs0 : 0 < Real.sqrt ‖(a 1 : p.adicCompletion ℚ)‖ := Real.sqrt_pos.mpr h1
  generalize ‖(a 1 : p.adicCompletion ℚ)‖ = B at *
  generalize Real.sqrt B = s at *
  subst hs
  field_simp

private theorem isLocallyConstant_sph : IsLocallyConstant (sph p) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ?_
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤ :
      Set (GL (Fin 2) (p.adicCompletion ℚ))),
    (isOpen_localLevelOne_top p).preimage (continuous_const.mul continuous_id), by simp,
    fun y hy => ?_⟩
  have hxy : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
  rw [hxy, sph_mul_right p hy]

private theorem sph_mem : sph p ∈ principalSeries2 p (chi p) :=
  mem_principalSeries2_iff.mpr ⟨isLocallyConstant_sph p, sph_upper_mul p, sph_diag_mul p⟩

private theorem sph_one : sph p 1 = 1 := by
  simp [sph]

private theorem chi_trivial :
    ∀ i, ∀ u ∈ higherUnitsAt ℚ p ((fun _ => 0 : Fin 2 → ℕ) i), chi p i u = 1 := by
  intro i u hu
  have hu1 : ‖(u : p.adicCompletion ℚ)‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr ((mem_higherUnitsAt_iff ℚ p).mp hu).1
  fin_cases i
  · rfl
  · ext
    simp [chi, normInvChar, hu1]

private theorem chi_dom :
    ‖((chi p 0 (AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p) : ℂˣ) : ℂ)‖ <
      ‖((chi p 1 (AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p) : ℂˣ) : ℂ)‖ := by
  have hlt : ‖(AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr (by
      rw [AdelicLevel.valued_uniformizerUnit]
      exact WithZero.exp_lt_one_iff.mpr (by norm_num))
  have hpos : 0 < ‖(AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ)‖ :=
    norm_pos_iff.mpr (Units.ne_zero _)
  simp only [chi, normInvChar]
  simpa [abs_of_pos (inv_pos.mpr hpos)] using (one_lt_inv₀ hpos).mpr hlt

/-- A nonvacuous instance: the characters `(1, ‖·‖⁻¹)` are trivial on the units of valuation `1`
and satisfy `‖χ₀(ϖ)‖ = 1 < ‖ϖ‖⁻¹ = ‖χ₁(ϖ)‖`, and the spherical vector `sph p`, which takes the
value `1` at the identity, lies in the principal series and is right invariant under the open
subgroup `localLevelOne (𝓞 ℚ) ℚ p ⊤`. So every hypothesis holds with `f ≠ 0`, and the theorem
bounds the Jacquet integral of `sph p`. -/
example [MeasurableSpace (p.adicCompletion ℚ)] [BorelSpace (p.adicCompletion ℚ)]
    (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure] :
    sph p 1 = 1 ∧ ∫⁻ y, ‖sph p (weyl p * unipotentGL2 y * 1)‖ₑ ∂ν < ∞ ∧
      ∃ C : ℝ≥0, ∀ k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ∫⁻ y, ‖sph p (weyl p * unipotentGL2 y * k)‖ₑ ∂ν ≤ C := by
  have h :=
    absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
      p (chi p) (fun _ => 0) (chi_trivial p) (AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p)
      (AdelicLevel.valued_uniformizerUnit (𝓞 ℚ) ℚ p) (chi_dom p) (sph p) (sph_mem p)
      ⟨_, isOpen_localLevelOne_top p, fun k hk g => sph_mul_right p hk g⟩ (weyl p) rfl ν
  exact ⟨sph_one p, h.1 1, h.2.2.2⟩

end JacquetIntegral2Test
