/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPage
public import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# The induced finite filtration on total homology

The horizontal filtration of a first-quadrant bicomplex induces, by taking
images of the maps on homology, a canonical filtration on total homology.
This file proves that the induced filtration is zero below degree zero and is
already exhaustive in homological degree `n` at stage `n`.  It also packages
the associated graded cokernel.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Homology in degree `n` of every stage of the complete horizontal
filtration. -/
noncomputable def horizontalCompleteHomologyDiagram (n : ℕ) : EInt ⥤ C :=
  (horizontalCompleteTotalFiltration K).diagram ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n

/-- Map from the homology of a complete filtration stage to total homology. -/
noncomputable def horizontalCompleteHomologyToTotal (n : ℕ) (i : EInt) :
    (horizontalCompleteHomologyDiagram K n).obj i ⟶
      (K.total (ComplexShape.down ℕ)).homology n :=
  HomologicalComplex.homologyMap
    ((horizontalCompleteTotalFiltration K).ι.app i) n

/-- The homology-to-total map is induced by the explicit complete-stage
inclusion. -/
theorem horizontalCompleteHomologyToTotal_eq (n : ℕ) (i : EInt) :
    horizontalCompleteHomologyToTotal K n i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalToTotal K i) n :=
  rfl

/-- Naturality of the maps from stage homology to total homology. -/
theorem horizontalCompleteHomologyToTotal_naturality (n : ℕ)
    {i j : EInt} (f : i ⟶ j) :
    (horizontalCompleteHomologyDiagram K n).map f ≫
        horizontalCompleteHomologyToTotal K n j =
      horizontalCompleteHomologyToTotal K n i := by
  change HomologicalComplex.homologyMap
        ((horizontalCompleteTotalFiltration K).diagram.map f) n ≫
      HomologicalComplex.homologyMap
        ((horizontalCompleteTotalFiltration K).ι.app j) n =
    HomologicalComplex.homologyMap
      ((horizontalCompleteTotalFiltration K).ι.app i) n
  rw [← HomologicalComplex.homologyMap_comp]
  rw [(horizontalCompleteTotalFiltration K).ι.naturality f]
  simp

/-- Stage homology maps packaged as a diagram in the overcategory of total
homology. -/
noncomputable def horizontalCompleteHomologyOverDiagram (n : ℕ) :
    EInt ⥤ Over ((K.total (ComplexShape.down ℕ)).homology n) :=
  (horizontalCompleteHomologyDiagram K n).toOver _
    (horizontalCompleteHomologyToTotal K n)
    (horizontalCompleteHomologyToTotal_naturality K n)

/-- The canonical filtration on total homology obtained by taking the images
of the stage-homology maps. -/
noncomputable def horizontalTotalHomologyFiltration (n : ℕ) :
    CategoryTheory.Filtration
      ((K.total (ComplexShape.down ℕ)).homology n) EInt where
  toMonoOver := horizontalCompleteHomologyOverDiagram K n ⋙ MonoOver.image

/-- Objects of the total-homology filtration are the corresponding images. -/
theorem horizontalTotalHomologyFiltration_obj (n : ℕ) (i : EInt) :
    (horizontalTotalHomologyFiltration K n).obj i =
      image (horizontalCompleteHomologyToTotal K n i) :=
  rfl

/-- Structure maps of the total-homology filtration are image inclusions. -/
theorem horizontalTotalHomologyFiltration_ι_app (n : ℕ) (i : EInt) :
    (horizontalTotalHomologyFiltration K n).ι.app i =
      image.ι (horizontalCompleteHomologyToTotal K n i) :=
  rfl

/-- At a nonnegative stage containing chain degree `n`, the map to total
homology in degree `n` is epic. -/
theorem horizontalCompleteHomologyToTotal_epi_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) (n : ℕ) (h : n ≤ a.toNat) :
    Epi (horizontalCompleteHomologyToTotal K n (a : EInt)) := by
  rw [horizontalCompleteHomologyToTotal_eq]
  have hmiddle : IsIso
      ((horizontalCompleteFilteredTotalToTotal K (a : EInt)).f n) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K a ha n h
  let _ := hmiddle
  have hnextmono : Mono
      ((horizontalCompleteFilteredTotalToTotal K (a : EInt)).f
        ((ComplexShape.down ℕ).next n)) := by
    change Mono (((if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K).arrow).f
      ((ComplexShape.down ℕ).next n))
    rw [ite_eq_left ha]
    change Mono ((horizontalFilteredTotalComplexToTotal K a.toNat).f
      ((ComplexShape.down ℕ).next n))
    infer_instance
  have hcycles : IsIso (HomologicalComplex.cyclesMap
      (horizontalCompleteFilteredTotalToTotal K (a : EInt)) n) := by
    exact ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
      ((HomologicalComplex.shortComplexFunctor C
        (ComplexShape.down ℕ) n).map
          (horizontalCompleteFilteredTotalToTotal K (a : EInt)))
      hmiddle hnextmono
  have hcyclesEpi : Epi (HomologicalComplex.cyclesMap
      (horizontalCompleteFilteredTotalToTotal K (a : EInt)) n) :=
    @IsIso.epi_of_iso _ _ _ _ _ hcycles
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap'
    ((HomologicalComplex.shortComplexFunctor C
      (ComplexShape.down ℕ) n).map
        (horizontalCompleteFilteredTotalToTotal K (a : EInt)))
    hcyclesEpi

/-- At a nonnegative stage containing degree `n`, the image subobject is all
of total homology. -/
theorem horizontalTotalHomologyFiltration_ι_app_isIso_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) (n : ℕ) (h : n ≤ a.toNat) :
    IsIso ((horizontalTotalHomologyFiltration K n).ι.app (a : EInt)) := by
  rw [horizontalTotalHomologyFiltration_ι_app]
  let _ : Epi (horizontalCompleteHomologyToTotal K n (a : EInt)) :=
    horizontalCompleteHomologyToTotal_epi_of_nonneg K a ha n h
  have : Epi (image.ι
      (horizontalCompleteHomologyToTotal K n (a : EInt))) :=
    epi_image_of_epi _
  exact isIso_of_mono_of_epi _

/-- In homological degree `n`, the induced filtration is exhaustive by stage
`n`. -/
theorem horizontalTotalHomologyFiltration_exhaustive (n : ℕ) :
    IsIso ((horizontalTotalHomologyFiltration K n).ι.app ((n : ℤ) : EInt)) :=
  horizontalTotalHomologyFiltration_ι_app_isIso_of_nonneg K (n : ℤ)
    (by omega) n (by simp)

/-- Stage `n+1` contains the complete three-term window computing homology in
degree `n`, so its map to total homology is an isomorphism. -/
theorem horizontalCompleteHomologyToTotal_isIso_succ (n : ℕ) :
    IsIso (horizontalCompleteHomologyToTotal K n (((n : ℤ) + 1) : EInt)) := by
  rw [horizontalCompleteHomologyToTotal_eq,
    ← quasiIsoAt_iff_isIso_homologyMap]
  have htoNat : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [quasiIsoAt_iff'
    (horizontalCompleteFilteredTotalToTotal K (((n : ℤ) + 1) : EInt))
    ((ComplexShape.down ℕ).prev n) n ((ComplexShape.down ℕ).next n) rfl rfl]
  have hprev : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (((n : ℤ) + 1) : EInt)).f ((ComplexShape.down ℕ).prev n)) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K
      ((n : ℤ) + 1) (by omega) _ (by rw [htoNat]; simp)
  have hmiddle : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (((n : ℤ) + 1) : EInt)).f n) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K
      ((n : ℤ) + 1) (by omega) _ (by rw [htoNat]; omega)
  have hnext : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (((n : ℤ) + 1) : EInt)).f ((ComplexShape.down ℕ).next n)) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K
      ((n : ℤ) + 1) (by omega) _ (by
        rw [htoNat]
        cases n with
        | zero => simp
        | succ n => simp; omega)
  let φ := ((HomologicalComplex.shortComplexFunctor' C
    (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n) n
      ((ComplexShape.down ℕ).next n)).map
        (horizontalCompleteFilteredTotalToTotal K
          (((n : ℤ) + 1) : EInt)))
  have hτ₁ : IsIso φ.τ₁ := by
    dsimp [φ]
    exact hprev
  have hτ₂ : IsIso φ.τ₂ := by
    dsimp [φ]
    exact hmiddle
  have hτ₃ : IsIso φ.τ₃ := by
    dsimp [φ]
    exact hnext
  have hτ₁Epi : Epi φ.τ₁ := @IsIso.epi_of_iso _ _ _ _ _ hτ₁
  have hτ₃Mono : Mono φ.τ₃ := @IsIso.mono_of_iso _ _ _ _ _ hτ₃
  let _ := hτ₁Epi
  let _ := hτ₂
  let _ := hτ₃Mono
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

/-- Every negative stage of the induced homology filtration is zero. -/
theorem horizontalTotalHomologyFiltration_obj_isZero_of_neg
    (a : ℤ) (ha : a < 0) (n : ℕ) :
    IsZero ((horizontalTotalHomologyFiltration K n).obj (a : EInt)) := by
  rw [horizontalTotalHomologyFiltration_obj]
  apply IsZero.of_epi
    (factorThruImage (horizontalCompleteHomologyToTotal K n (a : EInt)))
  change IsZero
    ((horizontalCompleteFilteredTotalComplex K (a : EInt)).homology n)
  have hstage : IsZero
      ((horizontalCompleteFilteredTotalComplex K (a : EInt)).homology n) := by
    rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a ha]
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_zero _)
  exact hstage

/-- The preceding finite filtration index is below the index of column `p`. -/
theorem horizontalTotalHomologyPrevIndex_le (p : ℕ) :
    (((p : ℤ) - 1 : ℤ) : EInt) ≤ ((p : ℤ) : EInt) :=
  WithBotTop.coe_monotone (by omega)

/-- Inclusion of consecutive induced homology-filtration stages in total
degree `p+q`. -/
noncomputable def horizontalTotalHomologyFiltrationStepMap (p q : ℕ) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        (((p : ℤ) - 1 : ℤ) : EInt) ⟶
      (horizontalTotalHomologyFiltration K (p + q)).obj
        ((p : ℤ) : EInt) :=
  (((horizontalTotalHomologyFiltration K (p + q)).toMonoOver.map
    (homOfLE (horizontalTotalHomologyPrevIndex_le p))).hom.left)

/-- Consecutive induced homology-filtration stages form a monomorphism. -/
noncomputable instance horizontalTotalHomologyFiltrationStepMap_mono
    (p q : ℕ) :
    Mono (horizontalTotalHomologyFiltrationStepMap K p q) := by
  apply mono_of_mono_fac
    (MonoOver.w ((horizontalTotalHomologyFiltration K (p + q)).toMonoOver.map
      (homOfLE (horizontalTotalHomologyPrevIndex_le p))))

/-- Associated graded piece of total homology at bidegree `(p,q)`. -/
noncomputable abbrev horizontalTotalHomologyGradedPiece (p q : ℕ) : C :=
  cokernel (horizontalTotalHomologyFiltrationStepMap K p q)

/-- The consecutive-stage inclusion and its cokernel form a short exact
sequence. -/
theorem horizontalTotalHomologyFiltrationStepShortExact (p q : ℕ) :
    (ShortComplex.cokernelSequence
      (horizontalTotalHomologyFiltrationStepMap K p q)).ShortExact := by
  have hm : Mono ((ShortComplex.cokernelSequence
      (horizontalTotalHomologyFiltrationStepMap K p q)).f) := by
    change Mono (horizontalTotalHomologyFiltrationStepMap K p q)
    infer_instance
  let _ := hm
  exact { exact := ShortComplex.cokernelSequence_exact _ }

end HomologicalComplex₂
