/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_AdelicHeight.lean`,
`Definitions/Def_AutomorphicForm_WindowedSiegelSet.lean`
and
`P2M/Sol/S_AutomorphicForm_adelicHeight_sigmaAdelicAct.lean`
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
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicLevel

/-!
# The adelic height on `GL₂`

For `g ∈ GL₂` over a normed field, the local heights compare `|det g|` with the size of the
bottom row `(c, d)` of `g`:

* `finLocalHeight g = |det g| / max(|c|, |d|)²`, used at finite places;
* `archLocalHeight g = |det g| / (|c|² + |d|²)`, used at infinite places.

The adelic height of `g ∈ GL₂(𝔸_F)` is the product of the archimedean local heights, each
raised to the multiplicity of its place, and of the finite local heights. All but finitely many
finite local heights are `1` (`hasFiniteMulSupport_finLocalHeight`): outside finitely many
places, the entries of `g` and of `g⁻¹` are integral.

`adelicHeight_map_of_norm_eq` shows that the adelic height is unchanged by a ring endomorphism
of the adele ring that permutes the places, preserving multiplicities and the norms of the
place components.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace NumberField.AdelicHeight

section Local

variable {K : Type*} [NormedField K]

/-- The max norm `max ‖M 1 0‖ ‖M 1 1‖` of the bottom row of a `2 × 2` matrix. -/
def rowMaxNorm (M : Matrix (Fin 2) (Fin 2) K) : ℝ := max ‖M 1 0‖ ‖M 1 1‖

/-- The squared Euclidean norm `‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2` of the bottom row of a `2 × 2`
matrix. -/
def rowNormSq (M : Matrix (Fin 2) (Fin 2) K) : ℝ := ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2

/-- The local height at a finite place: `‖det g‖ / max(‖c‖, ‖d‖) ^ 2` for the bottom row
`(c, d)` of `g`. -/
def finLocalHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2

/-- The local height at an infinite place: `‖det g‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2)` for the bottom row
`(c, d)` of `g`. -/
def archLocalHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowNormSq (g : Matrix (Fin 2) (Fin 2) K)

theorem rowMaxNorm_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ rowMaxNorm M :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem finLocalHeight_one : finLocalHeight (1 : GL (Fin 2) K) = 1 := by
  simp [finLocalHeight, rowMaxNorm]

theorem archLocalHeight_one : archLocalHeight (1 : GL (Fin 2) K) = 1 := by
  simp [archLocalHeight, rowNormSq]

/-- The finite local height only depends on the norms of the determinant and of the bottom
row. -/
theorem finLocalHeight_eq_of_norm_eq {K' : Type*} [NormedField K'] (g : GL (Fin 2) K)
    (h : GL (Fin 2) K')
    (hdet : ‖(h : Matrix (Fin 2) (Fin 2) K').det‖ = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖)
    (h₀ : ‖(h : Matrix (Fin 2) (Fin 2) K') 1 0‖ = ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖)
    (h₁ : ‖(h : Matrix (Fin 2) (Fin 2) K') 1 1‖ = ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖) :
    finLocalHeight h = finLocalHeight g := by
  unfold finLocalHeight rowMaxNorm
  rw [hdet, h₀, h₁]

/-- The archimedean local height only depends on the norms of the determinant and of the
bottom row. -/
theorem archLocalHeight_eq_of_norm_eq {K' : Type*} [NormedField K'] (g : GL (Fin 2) K)
    (h : GL (Fin 2) K')
    (hdet : ‖(h : Matrix (Fin 2) (Fin 2) K').det‖ = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖)
    (h₀ : ‖(h : Matrix (Fin 2) (Fin 2) K') 1 0‖ = ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖)
    (h₁ : ‖(h : Matrix (Fin 2) (Fin 2) K') 1 1‖ = ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖) :
    archLocalHeight h = archLocalHeight g := by
  unfold archLocalHeight rowNormSq
  rw [hdet, h₀, h₁]

section Ultrametric

variable [IsUltrametricDist K]

private theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) K} (h : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 0)).trans (h 1 1)
  · rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 1)).trans (h 1 0)

/-- Over an ultrametric field, the finite local height of `g` is `1` when every entry of `g`
and of `g⁻¹` has norm at most `1`. -/
theorem finLocalHeight_eq_one (g : GL (Fin 2) K)
    (h : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight g = 1 := by
  have hd : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h
  have hd' : ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, norm_one]
  have hdet1 : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    refine le_antisymm hd ?_
    by_contra hlt
    push Not at hlt
    have := (mul_le_of_le_one_right (norm_nonneg _) hd').trans_lt hlt
    rw [hprod] at this
    exact lt_irrefl _ this
  have hrow_le : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ≤ 1 := max_le (h 1 0) (h 1 1)
  have hrow_ge : 1 ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    by_contra hlt
    push Not at hlt
    have h10 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ < 1 := (le_max_left _ _).trans_lt hlt
    have h11 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ < 1 := (le_max_right _ _).trans_lt hlt
    have hlt' : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ < 1 := by
      rw [Matrix.det_fin_two, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 0)).trans_lt h11
      · rw [norm_neg, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 1)).trans_lt h10
    rw [hdet1] at hlt'
    exact lt_irrefl _ hlt'
  unfold finLocalHeight
  rw [hdet1, le_antisymm hrow_le hrow_ge, one_pow, div_one]

end Ultrametric

end Local

section Adelic

variable (F : Type*) [Field F] [NumberField F]

/-- The archimedean height: the product over the infinite places `v` of the local heights,
each raised to the multiplicity of `v`. -/
def archHeight (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ v : InfinitePlace F, archLocalHeight (archComponent F v g) ^ v.mult

/-- The finite height: the product over the finite places of the local heights. All but
finitely many factors are `1` (`hasFiniteMulSupport_finLocalHeight`). -/
def finHeight (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), finLocalHeight (finComponent (𝓞 F) F v g)

/-- The adelic height of `g ∈ GL₂(𝔸_F)`: the archimedean height of its infinite part times the
finite height of its finite part. -/
def adelicHeight (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) : ℝ :=
  archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g)

theorem adelicHeight_one : adelicHeight F 1 = 1 := by
  simp [adelicHeight, archHeight, finHeight, finLocalHeight_one, archLocalHeight_one]

variable {F}

private theorem norm_le_one_of_mem_adicCompletionIntegers {v : HeightOneSpectrum (𝓞 F)}
    {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx)

/-- At all but finitely many finite places `v`, the local height of `g` at `v` is `1`: outside
finitely many places, the entries of `g` and of `g⁻¹` are integral. -/
private theorem finLocalHeight_finComponent_eventually_eq_one
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      finLocalHeight (finComponent (𝓞 F) F v g) = 1 := by
  have hg : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hg' : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => (((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
        ∈ v.adicCompletionIntegers F)
      ∧ ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg i)).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg' i))
  filter_upwards [hall] with v hv
  refine finLocalHeight_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.1 i j)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.2 i j)

/-- The local heights in the finite height of `g` are `1` at all but finitely many finite
places, so `finHeight` is a finite product. -/
theorem hasFiniteMulSupport_finLocalHeight (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (fun v : HeightOneSpectrum (𝓞 F) =>
      finLocalHeight (finComponent (𝓞 F) F v g)).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (finLocalHeight_finComponent_eventually_eq_one g)

private theorem det_archComponent_glArch (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (v : InfinitePlace F) :
    ((archComponent F v (glArch (𝓞 F) F g) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion).det =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det.1 v :=
  (RingHom.map_det ((archEval F v).comp (adeleArch (𝓞 F) F)) _).symm

private theorem det_finComponent_glFin (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (w : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F w (glFin (𝓞 F) F g) : GL (Fin 2) (w.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det.2 w :=
  (RingHom.map_det ((finAdeleEval (𝓞 F) F w).comp (adeleFin (𝓞 F) F)) _).symm

private theorem det_map (φ : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F) F)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det =
      φ (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det :=
  (RingHom.map_det φ _).symm

/-- The adelic height is invariant under a ring endomorphism `φ` of the adele ring together with
bijections of the infinite and of the finite places that preserve multiplicities and carry
the norm of each place component of `a` to the norm of the corresponding component
of `φ a`. -/
theorem adelicHeight_map_of_norm_eq (φ : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F) F)
    (eInf : InfinitePlace F ≃ InfinitePlace F)
    (eFin : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F))
    (hmult : ∀ v, (eInf v).mult = v.mult)
    (hInf : ∀ v (a : AdeleRing (𝓞 F) F), ‖(φ a).1 (eInf v)‖ = ‖a.1 v‖)
    (hFin : ∀ w (a : AdeleRing (𝓞 F) F), ‖(φ a).2 (eFin w)‖ = ‖a.2 w‖)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    adelicHeight F (Matrix.GeneralLinearGroup.map φ g) = adelicHeight F g := by
  unfold adelicHeight archHeight finHeight
  congr 1
  · refine (Fintype.prod_equiv eInf _ _ fun v => ?_).symm
    rw [hmult]
    congr 1
    refine (archLocalHeight_eq_of_norm_eq _ _ ?_ ?_ ?_).symm
    · rw [det_archComponent_glArch, det_archComponent_glArch, det_map, hInf]
    · exact hInf v _
    · exact hInf v _
  · rw [← finprod_comp_equiv eFin]
    refine finprod_congr fun w => ?_
    refine finLocalHeight_eq_of_norm_eq _ _ ?_ ?_ ?_
    · rw [det_finComponent_glFin, det_finComponent_glFin, det_map, hFin]
    · exact hFin w _
    · exact hFin w _

end Adelic

end NumberField.AdelicHeight
