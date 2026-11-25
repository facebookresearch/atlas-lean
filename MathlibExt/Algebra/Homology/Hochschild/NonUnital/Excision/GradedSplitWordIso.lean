/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.SplitWordFiltration
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationZeroImage
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveFiltrationZeroImage
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Relative graded split-word coordinates

The relative kernel removes the all-quotient
coordinate from each fixed-count family. Below
the word-length bound all remaining colors are
retained; at and beyond it the layer is zero.
The equivalences use a ground-linear splitting
and arbitrary independent coefficient modules.
They describe graded terms, not a differential
or an excision homology identification.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

section NativeKernelTransport

variable {k : Type u} [CommRing k]
  {ι : Type w} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat.{z} k) c}

private def componentKernelEquiv (f : C ⟶ D) (i : ι) :
    (kernel f).X i ≃ₗ[k] LinearMap.ker (f.f i).hom :=
  ((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
    ModuleCat.kernelIsoKer (f.f i)).toLinearEquiv

private theorem componentKernelEquiv_val (f : C ⟶ D) (i : ι)
    (x : (kernel f).X i) :
    (componentKernelEquiv f i x : C.X i) = ((kernel.ι f).f i).hom x := by
  have hcat :
      ((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
          ModuleCat.kernelIsoKer (f.f i)).hom ≫
        ModuleCat.ofHom ((LinearMap.ker ((f.f i).hom)).subtype) = (kernel.ι f).f i := by
    simp only [Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
      PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι f (HomologicalComplex.eval (ModuleCat.{z} k) c i)
  have hx := congrArg
    (fun g : (kernel f).X i ⟶ C.X i => g.hom x) hcat
  have hmap : (componentKernelEquiv f i).toLinearMap =
      (((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
        ModuleCat.kernelIsoKer (f.f i)).hom).hom :=
    CategoryTheory.Iso.toLinearMap_toLinearEquiv _
  have he : componentKernelEquiv f i x =
      (((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
        ModuleCat.kernelIsoKer (f.f i)).hom).hom x := DFunLike.congr_fun hmap x
  apply (congrArg (fun y : LinearMap.ker (f.f i).hom => y.val) he).trans
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    Submodule.subtype_apply] using hx

variable {M Q W T : Type z} [AddCommGroup M] [Module k M]
  [AddCommGroup Q] [Module k Q] [AddCommGroup W] [Module k W]
  [AddCommGroup T] [Module k T]

private theorem kernelWordTransport_eq (f : M →ₗ[k] Q) (q : W →ₗ[k] T)
    (e : M ≃ₗ[k] W) (t : Q ≃ₗ[k] T)
    (h : t.toLinearMap.comp f = q.comp e.toLinearMap) :
    LinearMap.ker f = (LinearMap.ker q).comap e.toLinearMap := by
  apply Submodule.ext
  intro x
  change f x = 0 ↔ q (e x) = 0
  have hx := congrArg (fun g : M →ₗ[k] T => g x) h
  change t (f x) = q (e x) at hx
  rw [← hx]
  constructor
  · intro hf
    rw [hf, map_zero]
  · intro ht
    apply t.injective
    simpa only [map_zero] using ht

end NativeKernelTransport

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (splitting : I.KSplit)

/-- The original quotient tensor map in every original word position. -/
def originalQuotientWordMap (N : ℕ) :
    TensorPower k N A →ₗ[k] TensorPower k N I.Quotient :=
  PiTensorProduct.map (fun _ : Fin N => NonUnitalSubalgebra.Quotient.mkL I)

private theorem naiveQuotient_word_natural (n : ℕ) :
    (TensorPower.consEquiv k I.Quotient n).toLinearMap.comp
        ((cyclicBComplexHom I.quotientMap).f n).hom =
      (originalQuotientWordMap k A I (n + 1)).comp
        (TensorPower.consEquiv k A n).toLinearMap := by
  rw [cyclicBComplexHom_f]
  exact TensorPower.consEquiv_naturality (NonUnitalSubalgebra.Quotient.mkL I) n

/-- The evaluated original naive kernel, in its word coordinates. -/
def relativeNaiveWordKernelEquiv (n : ℕ) :
    (relativeNaiveComplex k A I).X n ≃ₗ[k]
      LinearMap.ker (originalQuotientWordMap k A I (n + 1)) :=
  ((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n)
      (cyclicBComplexHom I.quotientMap)) ≪≫
    ModuleCat.kernelIsoKer ((cyclicBComplexHom I.quotientMap).f n)).toLinearEquiv.trans
      ((LinearEquiv.ofEq _ _ (by
        exact kernelWordTransport_eq ((cyclicBComplexHom I.quotientMap).f n).hom
          (originalQuotientWordMap k A I (n + 1))
          (TensorPower.consEquiv k A n) (TensorPower.consEquiv k I.Quotient n)
          (naiveQuotient_word_natural k A I n))).trans
        ((TensorPower.consEquiv k A n).ofSubmodule'
          (LinearMap.ker (originalQuotientWordMap k A I (n + 1)))))

/-- This native kernel equivalence has exactly the original relative naive word getter. -/
theorem relativeNaiveWordKernelEquiv_val (n : ℕ)
    (x : (relativeNaiveComplex k A I).X n) :
    (relativeNaiveWordKernelEquiv k A I n x : TensorPower k (n + 1) A) =
      relativeNaiveWordMap k A I n x := by
  rw [relativeNaiveWordKernelEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.ofSubmodule'_apply, LinearEquiv.coe_ofEq_apply]
  change TensorPower.consEquiv k A n
      (componentKernelEquiv (cyclicBComplexHom I.quotientMap) n x : (bComplex k A).X n) =
    relativeNaiveWordMap k A I n x
  rw [componentKernelEquiv_val]
  rfl

/-- The all-quotient coordinate vanishes on the original relative naive kernel. -/
theorem relativeNaiveWord_allQuotient_zero (n : ℕ)
    (colour : Fin (n + 1) → Bool) (hc : colour = fun _ => true)
    (x : (relativeNaiveComplex k A I).X n) :
    splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x) = 0 := by
  subst colour
  change originalQuotientWordMap k A I (n + 1) (relativeNaiveWordMap k A I n x) = 0
  rw [← relativeNaiveWordKernelEquiv_val k A I n x]
  exact (relativeNaiveWordKernelEquiv k A I n x).property

/-- The full source-count family with precisely its original all-quotient coordinate zero. -/
def naiveRelativeSplitWordGradeSpace (p n : ℕ) :
    Submodule k (naiveSplitWordGradeCoordinates k A I p n) where
  carrier := {y | ∀ colour : splitWordGradeColours p (n + 1),
    colour.val = (fun _ => true) → y colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : splitWordTensor k A I colour.val)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' r x hx colour hc := by
    change r • x colour = (0 : splitWordTensor k A I colour.val)
    rw [hx colour hc, smul_zero]

/-- The native module of all original fixed-p relative naive coordinates. -/
abbrev naiveRelativeSplitWordGradeCoordinates (p n : ℕ) :=
  naiveRelativeSplitWordGradeSpace k A I p n

/-- Sum every original source-count colour using its original section/inclusion word map. -/
def naiveFixedGradeToAmbient (p n : ℕ) :
    naiveSplitWordGradeCoordinates k A I p n →ₗ[k] TensorPower k (n + 1) A :=
  ∑ colour : splitWordGradeColours p (n + 1),
    (splitWordToAmbient k A I splitting colour.val).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_apply (p n : ℕ)
    (y : naiveSplitWordGradeCoordinates k A I p n) :
    naiveFixedGradeToAmbient k A I splitting p n y =
      ∑ colour : splitWordGradeColours p (n + 1),
        splitWordToAmbient k A I splitting colour.val (y colour) := by
  simp only [naiveFixedGradeToAmbient, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_coordinate (p n : ℕ)
    (y : naiveSplitWordGradeCoordinates k A I p n)
    (target : splitWordGradeColours p (n + 1)) :
    splitAmbientToWord k A I splitting target.val
        (naiveFixedGradeToAmbient k A I splitting p n y) = y target := by
  classical
  rw [naiveFixedGradeToAmbient_apply, map_sum]
  have ht (source : splitWordGradeColours p (n + 1)) :
      splitAmbientToWord k A I splitting target.val
          (splitWordToAmbient k A I splitting source.val (y source)) =
        if source = target then y target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (y target))
        (splitAmbientToWord_comp_splitWordToAmbient k A I splitting target.val)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (y source))
        (splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting source.val target.val
          (fun hv => h (Subtype.ext hv)))
  simp_rw [ht]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_quotient_zero (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    originalQuotientWordMap k A I (n + 1)
      (naiveFixedGradeToAmbient k A I splitting p n y.val) = 0 := by
  classical
  rw [naiveFixedGradeToAmbient_apply, map_sum]
  apply Finset.sum_eq_zero
  intro colour _
  by_cases hc : colour.val = fun _ => true
  · rw [y.property colour hc, map_zero, map_zero]
  · change splitAmbientToWord k A I splitting (fun _ : Fin (n + 1) => true)
      (splitWordToAmbient k A I splitting colour.val (y.val colour)) = 0
    exact congrArg (fun f => f (y.val colour))
      (splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting colour.val
        (fun _ => true) hc)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_mem_span (p n : ℕ)
    (y : naiveSplitWordGradeCoordinates k A I p n) :
    naiveFixedGradeToAmbient k A I splitting p n y ∈
      idealWordSpan k A I (n + 1) (n + 1 - p) := by
  classical
  rw [naiveFixedGradeToAmbient_apply]
  apply Submodule.sum_mem
  intro colour _
  have hc := splitWordPositionCounts_add colour.val
  have hq := colour.property
  have hrequired : n + 1 - p ≤ splitWordIdealPositionCount colour.val := by omega
  exact splitWordToAmbient_range_le_idealWordSpan k A I splitting colour.val (n + 1 - p)
    hrequired ⟨y colour, rfl⟩

/-- Every reconstructed source-count family lies in the original quotient kernel. -/
def naiveFixedGradeToKernel (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k]
      LinearMap.ker (originalQuotientWordMap k A I (n + 1)) :=
  ((naiveFixedGradeToAmbient k A I splitting p n).comp
    (naiveRelativeSplitWordGradeSpace k A I p n).subtype).codRestrict
      (LinearMap.ker (originalQuotientWordMap k A I (n + 1)))
      (by
        intro y
        exact naiveFixedGradeToAmbient_quotient_zero k A I splitting p n y)

/-- Native evaluated-kernel transport returns the original relative naive term. -/
def naiveFixedGradeToRelative (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k]
      (relativeNaiveComplex k A I).X n :=
  (relativeNaiveWordKernelEquiv k A I n).symm.toLinearMap.comp
    (naiveFixedGradeToKernel k A I splitting p n)

private theorem naiveFixedGradeToRelative_word (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    relativeNaiveWordMap k A I n (naiveFixedGradeToRelative k A I splitting p n y) =
      naiveFixedGradeToAmbient k A I splitting p n y.val := by
  have h := congrArg (fun z : LinearMap.ker (originalQuotientWordMap k A I (n + 1)) => z.val)
    ((relativeNaiveWordKernelEquiv k A I n).apply_symm_apply
      (naiveFixedGradeToKernel k A I splitting p n y))
  rw [relativeNaiveWordKernelEquiv_val] at h
  exact h

/-- Actual reconstruction into the original naive count stage, through its original relative kernel. -/
def naiveFixedGradeToStage (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k] naiveWordFiltration k A I p n :=
  (naiveFixedGradeToRelative k A I splitting p n).codRestrict (naiveWordFiltration k A I p n)
    (fun y => by
      change relativeNaiveWordMap k A I n (naiveFixedGradeToRelative k A I splitting p n y) ∈
        idealWordSpan k A I (n + 1) (n + 1 - p)
      rw [naiveFixedGradeToRelative_word]
      exact naiveFixedGradeToAmbient_mem_span k A I splitting p n y.val)

/-- The reconstructed original stage has exactly the finite sum of every original source-count word. -/
theorem naiveFixedGradeToStage_word (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    relativeNaiveWordMap k A I n ((naiveFixedGradeToStage k A I splitting p n y).val) =
      ∑ colour : splitWordGradeColours p (n + 1),
        splitWordToAmbient k A I splitting colour.val (y.val colour) := by
  exact (naiveFixedGradeToRelative_word k A I splitting p n y).trans
    (naiveFixedGradeToAmbient_apply k A I splitting p n y.val)

/-- Original naive stage extraction, retaining the exact original relative-kernel coordinate condition. -/
def naiveStageToRelativeFixedGrade (p n : ℕ) :
    naiveWordFiltration k A I p n →ₗ[k] naiveRelativeSplitWordGradeCoordinates k A I p n :=
  (LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    naiveStageToSplitWord k A I splitting p n colour.val)).codRestrict
      (naiveRelativeSplitWordGradeSpace k A I p n) (fun x colour hc =>
        relativeNaiveWord_allQuotient_zero k A I splitting n colour.val hc x.val)

private theorem naiveStageToRelativeFixedGrade_reconstruct (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    naiveStageToRelativeFixedGrade k A I splitting p n
        (naiveFixedGradeToStage k A I splitting p n y) = y := by
  apply Subtype.ext
  funext colour
  change splitAmbientToWord k A I splitting colour.val
    (relativeNaiveWordMap k A I n (naiveFixedGradeToRelative k A I splitting p n y)) = y.val colour
  rw [naiveFixedGradeToRelative_word]
  exact naiveFixedGradeToAmbient_coordinate k A I splitting p n y.val colour

/-- The exact kernel of complete original naive source-count extraction is the original predecessor. -/
theorem naiveStageToRelativeFixedGrade_ker (p n : ℕ) :
    LinearMap.ker (naiveStageToRelativeFixedGrade k A I splitting p n) =
      (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype := by
  classical
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    change naiveStageToRelativeFixedGrade k A I splitting p n x = 0 at hx
    have hfixed (colour : splitWordGradeColours p (n + 1)) :
        naiveStageToSplitWord k A I splitting p n colour.val x = 0 :=
      congrArg (fun y : naiveRelativeSplitWordGradeCoordinates k A I p n => y.val colour) hx
    by_cases hp : p = 0
    · have hall (colour : Fin (n + 1) → Bool) :
          splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x.val) = 0 := by
        by_cases hc : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hc⟩
        · have hgt : p < quotientEntryCount colour := by omega
          exact naiveStageToSplitWord_zero_of_quotient_count k A I splitting p n colour hgt x
      have hw : relativeNaiveWordMap k A I n x.val = 0 := by
        have h := (splitWord_reconstruct k A I splitting (relativeNaiveWordMap k A I n x.val)).symm
        simpa only [hall, map_zero, Finset.sum_const_zero] using h
      have hx0 : x.val = 0 := (relativeNaiveWordMap_injective k A I n)
        (hw.trans (map_zero (relativeNaiveWordMap k A I n)).symm)
      change (naiveWordFiltration k A I p n).subtype x ∈ naiveLowerFiltration k A I p n
      rw [naiveLowerFiltration, ite_eq_left hp]
      simpa only [Submodule.mem_bot, Submodule.subtype_apply] using hx0
    · have hw : relativeNaiveWordMap k A I n x.val ∈
          idealWordSpan k A I (n + 1) (n + 1 - (p - 1)) := by
        rw [idealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting]
        change ∀ colour : Fin (n + 1) → Bool,
          splitWordIdealPositionCount colour < n + 1 - (p - 1) →
            splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x.val) = 0
        intro colour hc
        by_cases hq : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hq⟩
        · have hcount := splitWordPositionCounts_add colour
          have hgt : p < quotientEntryCount colour := by omega
          exact naiveStageToSplitWord_zero_of_quotient_count k A I splitting p n colour hgt x
      change (naiveWordFiltration k A I p n).subtype x ∈ naiveLowerFiltration k A I p n
      rw [naiveLowerFiltration, ite_eq_right hp]
      exact hw
  · intro hx
    change naiveStageToRelativeFixedGrade k A I splitting p n x = 0
    apply Subtype.ext
    funext colour
    exact naiveLowerFiltration_le_ker_stageToSplitWord k A I splitting p n colour.val colour.property hx

/-- Complete extraction from the original naive layer, with its all-quotient coordinate zero. -/
def naiveLayerToRelativeFixedGrade (p n : ℕ) :
    naiveWordLayer k A I p n →ₗ[k] naiveRelativeSplitWordGradeCoordinates k A I p n :=
  (naiveLayerToSplitWordCoordinates k A I splitting p n).codRestrict
    (naiveRelativeSplitWordGradeSpace k A I p n) (fun z => by
      refine Submodule.Quotient.induction_on _ z ?_
      intro x colour hc
      change splitAmbientToWord k A I splitting colour.val (relativeNaiveWordMap k A I n x.val) = 0
      exact relativeNaiveWord_allQuotient_zero k A I splitting n colour.val hc x.val)

private theorem naiveLayerToRelativeFixedGrade_projection (p n : ℕ)
    (x : naiveWordFiltration k A I p n) :
    naiveLayerToRelativeFixedGrade k A I splitting p n (naiveWordLayerProjection k A I p n x) =
      naiveStageToRelativeFixedGrade k A I splitting p n x := rfl

/-- The original naive quotient projection follows original-kernel reconstruction. -/
def naiveRelativeFixedGradeToLayer (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k] naiveWordLayer k A I p n :=
  (naiveWordLayerProjection k A I p n).comp (naiveFixedGradeToStage k A I splitting p n)

/-- Every original source-count naive coordinate is recovered by original stage/layer reconstruction. -/
theorem naiveLayerToRelativeFixedGrade_comp_inverse (p n : ℕ) :
    (naiveLayerToRelativeFixedGrade k A I splitting p n).comp
        (naiveRelativeFixedGradeToLayer k A I splitting p n) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  change naiveLayerToRelativeFixedGrade k A I splitting p n
    (naiveWordLayerProjection k A I p n (naiveFixedGradeToStage k A I splitting p n y)) = y
  rw [naiveLayerToRelativeFixedGrade_projection]
  exact naiveStageToRelativeFixedGrade_reconstruct k A I splitting p n y

/-- Native quotient equality identifies reconstructed complete naive coordinates with the original layer. -/
theorem naiveRelativeFixedGradeToLayer_comp_extraction (p n : ℕ) :
    (naiveRelativeFixedGradeToLayer k A I splitting p n).comp
        (naiveLayerToRelativeFixedGrade k A I splitting p n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro x
  change naiveWordLayerProjection k A I p n
      (naiveFixedGradeToStage k A I splitting p n
        (naiveLayerToRelativeFixedGrade k A I splitting p n (naiveWordLayerProjection k A I p n x))) =
    naiveWordLayerProjection k A I p n x
  rw [naiveLayerToRelativeFixedGrade_projection]
  have hzero : naiveStageToRelativeFixedGrade k A I splitting p n
      (naiveFixedGradeToStage k A I splitting p n
        (naiveStageToRelativeFixedGrade k A I splitting p n x) - x) = 0 := by
    rw [map_sub, naiveStageToRelativeFixedGrade_reconstruct, sub_self]
  have hl : naiveFixedGradeToStage k A I splitting p n
        (naiveStageToRelativeFixedGrade k A I splitting p n x) - x ∈
      (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype := by
    rw [← naiveStageToRelativeFixedGrade_ker k A I splitting p n]
    exact hzero
  exact (Submodule.Quotient.eq _).mpr hl

/-- The source splitting earns the exact equivalence of the original naive graded term
and all relative source-count coordinates. -/
def naiveGradedSplitWordIso (p n : ℕ) :
    naiveWordLayer k A I p n ≃ₗ[k] naiveRelativeSplitWordGradeCoordinates k A I p n :=
  { naiveLayerToRelativeFixedGrade k A I splitting p n with
    invFun := naiveRelativeFixedGradeToLayer k A I splitting p n
    left_inv := fun x => congrArg (fun f => f x)
      (naiveRelativeFixedGradeToLayer_comp_extraction k A I splitting p n)
    right_inv := fun y => congrArg (fun f => f y)
      (naiveLayerToRelativeFixedGrade_comp_inverse k A I splitting p n) }

/-- The forward graded equivalence retains precisely the accepted complete original naive extraction. -/
theorem naiveGradedSplitWordIso_apply (p n : ℕ) (z : naiveWordLayer k A I p n) :
    (naiveGradedSplitWordIso k A I splitting p n z).val =
      naiveLayerToSplitWordCoordinates k A I splitting p n z := rfl

/-- The inverse uses the original naive kernel and original quotient projection. -/
theorem naiveGradedSplitWordIso_symm_apply (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    (naiveGradedSplitWordIso k A I splitting p n).symm y =
      naiveWordLayerProjection k A I p n (naiveFixedGradeToStage k A I splitting p n y) := rfl

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- The original arbitrary-coefficient quotient tensor map keeps V under its identity. -/
def originalCoefficientQuotientWordMap (N : ℕ) :
    V ⊗[k] TensorPower k N A →ₗ[k] V ⊗[k] TensorPower k N I.Quotient :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V) (originalQuotientWordMap k A I N)

private theorem barQuotient_word_natural (n : ℕ) :
    (positiveBarWordIso k I.Quotient V n).hom.hom.comp
        ((positiveBarQuotientMap k A I V).f (n + 1)).hom =
      (originalCoefficientQuotientWordMap k A I V (n + 1)).comp
        (positiveBarWordIso k A V n).hom.hom := by
  let e : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 1
  let es : (positiveBarComplex k A V).X (n + 1) ≅ (barComplex k A V).X n :=
    (barComplex k A V).extendXIso e (i := n) rfl
  let et : (positiveBarComplex k I.Quotient V).X (n + 1) ≅ (barComplex k I.Quotient V).X n :=
    (barComplex k I.Quotient V).extendXIso e (i := n) rfl
  let cs : (barComplex k A V).X n ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) :=
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)).toModuleIso
  let ct : (barComplex k I.Quotient V).X n ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) I.Quotient) :=
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k I.Quotient n)).toModuleIso
  have hmap : (positiveBarQuotientMap k A I V).f (n + 1) =
      es.hom ≫ (barAlgebraMap (V := V) I.quotientMap).f n ≫ et.inv :=
    HomologicalComplex.extendMap_f (barAlgebraMap (V := V) I.quotientMap) e (i := n) rfl
  have hcoords : (barAlgebraMap (V := V) I.quotientMap).f n ≫ ct.hom =
      cs.hom ≫ ModuleCat.ofHom (originalCoefficientQuotientWordMap k A I V (n + 1)) := by
    apply ModuleCat.hom_ext
    change (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k I.Quotient n)).toLinearMap.comp
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (TensorPower.consLevelMap (NonUnitalSubalgebra.Quotient.mkL I) n)) =
      (originalCoefficientQuotientWordMap k A I V (n + 1)).comp
        (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)).toLinearMap
    apply TensorProduct.ext' (M := V) (N := A ⊗[k] TensorPower k n A)
    intro v x
    change TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k I.Quotient n)
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (TensorPower.consLevelMap (NonUnitalSubalgebra.Quotient.mkL I) n) (v ⊗ₜ[k] x)) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V) (originalQuotientWordMap k A I (n + 1))
        (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n) (v ⊗ₜ[k] x))
    rw [TensorProduct.map_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
      TensorProduct.map_tmul]
    have h := congrArg (fun f => f x)
      (TensorPower.consEquiv_naturality (NonUnitalSubalgebra.Quotient.mkL I) n)
    exact congrArg (fun y => v ⊗ₜ[k] y) h
  have hcat : (positiveBarQuotientMap k A I V).f (n + 1) ≫
        (positiveBarWordIso k I.Quotient V n).hom =
      (positiveBarWordIso k A V n).hom ≫
        ModuleCat.ofHom (originalCoefficientQuotientWordMap k A I V (n + 1)) := by
    change (positiveBarQuotientMap k A I V).f (n + 1) ≫ (et.hom ≫ ct.hom) =
      (es.hom ≫ cs.hom) ≫ ModuleCat.ofHom (originalCoefficientQuotientWordMap k A I V (n + 1))
    rw [hmap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hcoords]
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
    congrArg (fun f => f.hom) hcat

/-- The original evaluated positive kernel in its exact arbitrary-coefficient word coordinates. -/
def relativeBarWordKernelEquiv (n : ℕ) :
    (relativePositiveBarComplex k A I V).X (n + 1) ≃ₗ[k]
      LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)) :=
  ((PreservesKernel.iso
      (HomologicalComplex.eval (ModuleCat.{max u v w} k) (ComplexShape.down ℕ) (n + 1))
      (positiveBarQuotientMap k A I V)) ≪≫
    ModuleCat.kernelIsoKer ((positiveBarQuotientMap k A I V).f (n + 1))).toLinearEquiv.trans
      ((LinearEquiv.ofEq _ _ (by
        exact kernelWordTransport_eq ((positiveBarQuotientMap k A I V).f (n + 1)).hom
          (originalCoefficientQuotientWordMap k A I V (n + 1))
          (positiveBarWordIso k A V n).toLinearEquiv (positiveBarWordIso k I.Quotient V n).toLinearEquiv
          (barQuotient_word_natural k A I V n))).trans
        ((positiveBarWordIso k A V n).toLinearEquiv.ofSubmodule'
          (LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)))))

/-- The native positive kernel equivalence is precisely the original arbitrary-coefficient word getter. -/
theorem relativeBarWordKernelEquiv_val (n : ℕ)
    (x : (relativePositiveBarComplex k A I V).X (n + 1)) :
    (relativeBarWordKernelEquiv k A I V n x : V ⊗[k] TensorPower k (n + 1) A) =
      relativePositiveBarWordMap k A I V n x := by
  rw [relativeBarWordKernelEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.ofSubmodule'_apply, LinearEquiv.coe_ofEq_apply]
  change (positiveBarWordIso k A V n).toLinearEquiv
      (componentKernelEquiv (positiveBarQuotientMap k A I V) (n + 1) x :
        (positiveBarComplex k A V).X (n + 1)) =
    relativePositiveBarWordMap k A I V n x
  rw [componentKernelEquiv_val, CategoryTheory.Iso.toLinearEquiv_apply]
  rfl

/-- The original positive relative kernel has zero all-quotient coordinate, retaining V. -/
theorem relativeBarWord_allQuotient_zero (n : ℕ)
    (colour : Fin (n + 1) → Bool) (hc : colour = fun _ => true)
    (x : (relativePositiveBarComplex k A I V).X (n + 1)) :
    coefficientSplitAmbientToWord k A I V splitting colour (relativePositiveBarWordMap k A I V n x) = 0 := by
  subst colour
  change originalCoefficientQuotientWordMap k A I V (n + 1) (relativePositiveBarWordMap k A I V n x) = 0
  rw [← relativeBarWordKernelEquiv_val k A I V n x]
  exact (relativeBarWordKernelEquiv k A I V n x).property

/-- Every original source-count coefficient colour, with only its original all-quotient coordinate zero. -/
def barRelativeSplitWordGradeSpace (p n : ℕ) :
    Submodule k (barSplitWordGradeCoordinates k A I V p n) where
  carrier := {y | ∀ colour : splitWordGradeColours p (n + 1),
    colour.val = (fun _ => true) → y colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : V ⊗[k] splitWordTensor k A I colour.val)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' r x hx colour hc := by
    change r • x colour = (0 : V ⊗[k] splitWordTensor k A I colour.val)
    rw [hx colour hc, smul_zero]

/-- The full fixed-p positive relative coordinate module, with independent coefficient V. -/
abbrev barRelativeSplitWordGradeCoordinates (p n : ℕ) := barRelativeSplitWordGradeSpace k A I V p n

/-- Every original fixed-p coefficient word participates in the ambient reconstruction. -/
def barFixedGradeToAmbient (p n : ℕ) :
    barSplitWordGradeCoordinates k A I V p n →ₗ[k] V ⊗[k] TensorPower k (n + 1) A :=
  ∑ colour : splitWordGradeColours p (n + 1),
    (coefficientSplitWordToAmbient k A I V splitting colour.val).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_apply (p n : ℕ)
    (y : barSplitWordGradeCoordinates k A I V p n) :
    barFixedGradeToAmbient k A I splitting V p n y =
      ∑ colour : splitWordGradeColours p (n + 1),
        coefficientSplitWordToAmbient k A I V splitting colour.val (y colour) := by
  simp only [barFixedGradeToAmbient, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_coordinate (p n : ℕ)
    (y : barSplitWordGradeCoordinates k A I V p n) (target : splitWordGradeColours p (n + 1)) :
    coefficientSplitAmbientToWord k A I V splitting target.val
        (barFixedGradeToAmbient k A I splitting V p n y) = y target := by
  classical
  rw [barFixedGradeToAmbient_apply, map_sum]
  have ht (source : splitWordGradeColours p (n + 1)) :
      coefficientSplitAmbientToWord k A I V splitting target.val
          (coefficientSplitWordToAmbient k A I V splitting source.val (y source)) =
        if source = target then y target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (y target))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient k A I V splitting target.val)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (y source))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
          k A I V splitting source.val target.val (fun hv => h (Subtype.ext hv)))
  simp_rw [ht]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_quotient_zero (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    originalCoefficientQuotientWordMap k A I V (n + 1)
      (barFixedGradeToAmbient k A I splitting V p n y.val) = 0 := by
  classical
  rw [barFixedGradeToAmbient_apply, map_sum]
  apply Finset.sum_eq_zero
  intro colour _
  by_cases hc : colour.val = fun _ => true
  · rw [y.property colour hc, map_zero, map_zero]
  · change coefficientSplitAmbientToWord k A I V splitting (fun _ : Fin (n + 1) => true)
      (coefficientSplitWordToAmbient k A I V splitting colour.val (y.val colour)) = 0
    exact congrArg (fun f => f (y.val colour))
      (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
        k A I V splitting colour.val (fun _ => true) hc)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_mem_span (p n : ℕ)
    (y : barSplitWordGradeCoordinates k A I V p n) :
    barFixedGradeToAmbient k A I splitting V p n y ∈
      coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p) := by
  classical
  rw [barFixedGradeToAmbient_apply]
  apply Submodule.sum_mem
  intro colour _
  have hc := splitWordPositionCounts_add colour.val
  have hq := colour.property
  have hrequired : n + 1 - p ≤ splitWordIdealPositionCount colour.val := by omega
  exact coefficientSplitWordToAmbient_range_le_coefficientIdealWordSpan
    k A I splitting V colour.val (n + 1 - p) hrequired ⟨y colour, rfl⟩

/-- Every original coefficient reconstruction lies in the original positive quotient kernel. -/
def barFixedGradeToKernel (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k]
      LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)) :=
  ((barFixedGradeToAmbient k A I splitting V p n).comp
    (barRelativeSplitWordGradeSpace k A I V p n).subtype).codRestrict
      (LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)))
      (by
        intro y
        exact barFixedGradeToAmbient_quotient_zero k A I splitting V p n y)

/-- Native evaluated-kernel transport retains the original positive term and coefficient. -/
def barFixedGradeToRelative (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k]
      (relativePositiveBarComplex k A I V).X (n + 1) :=
  (relativeBarWordKernelEquiv k A I V n).symm.toLinearMap.comp
    (barFixedGradeToKernel k A I splitting V p n)

private theorem barFixedGradeToRelative_word (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    relativePositiveBarWordMap k A I V n (barFixedGradeToRelative k A I splitting V p n y) =
      barFixedGradeToAmbient k A I splitting V p n y.val := by
  have h := congrArg
    (fun z : LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)) => z.val)
    ((relativeBarWordKernelEquiv k A I V n).apply_symm_apply
      (barFixedGradeToKernel k A I splitting V p n y))
  rw [relativeBarWordKernelEquiv_val] at h
  exact h

/-- Actual arbitrary-coefficient reconstruction into the original positive count stage and relative kernel. -/
def barFixedGradeToStage (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k] barWordFiltration k A I V p n :=
  (barFixedGradeToRelative k A I splitting V p n).codRestrict (barWordFiltration k A I V p n)
    (fun y => by
      change relativePositiveBarWordMap k A I V n (barFixedGradeToRelative k A I splitting V p n y) ∈
        coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p)
      rw [barFixedGradeToRelative_word]
      exact barFixedGradeToAmbient_mem_span k A I splitting V p n y.val)

/-- Every reconstructed coefficient stage word is its original complete source-count colour sum. -/
theorem barFixedGradeToStage_word (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    relativePositiveBarWordMap k A I V n ((barFixedGradeToStage k A I splitting V p n y).val) =
      ∑ colour : splitWordGradeColours p (n + 1),
        coefficientSplitWordToAmbient k A I V splitting colour.val (y.val colour) := by
  exact (barFixedGradeToRelative_word k A I splitting V p n y).trans
    (barFixedGradeToAmbient_apply k A I splitting V p n y.val)

/-- Original positive stage extraction retains the all-quotient kernel condition and coefficient identity. -/
def barStageToRelativeFixedGrade (p n : ℕ) :
    barWordFiltration k A I V p n →ₗ[k] barRelativeSplitWordGradeCoordinates k A I V p n :=
  (LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    barStageToSplitWord k A I splitting V p n colour.val)).codRestrict
      (barRelativeSplitWordGradeSpace k A I V p n) (fun x colour hc =>
        relativeBarWord_allQuotient_zero k A I splitting V n colour.val hc x.val)

private theorem barStageToRelativeFixedGrade_reconstruct (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    barStageToRelativeFixedGrade k A I splitting V p n
        (barFixedGradeToStage k A I splitting V p n y) = y := by
  apply Subtype.ext
  funext colour
  change coefficientSplitAmbientToWord k A I V splitting colour.val
    (relativePositiveBarWordMap k A I V n (barFixedGradeToRelative k A I splitting V p n y)) = y.val colour
  rw [barFixedGradeToRelative_word]
  exact barFixedGradeToAmbient_coordinate k A I splitting V p n y.val colour

/-- The complete original positive source-count extraction has exactly its original predecessor as kernel. -/
theorem barStageToRelativeFixedGrade_ker (p n : ℕ) :
    LinearMap.ker (barStageToRelativeFixedGrade k A I splitting V p n) =
      (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype := by
  classical
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    change barStageToRelativeFixedGrade k A I splitting V p n x = 0 at hx
    have hfixed (colour : splitWordGradeColours p (n + 1)) :
        barStageToSplitWord k A I splitting V p n colour.val x = 0 :=
      congrArg (fun y : barRelativeSplitWordGradeCoordinates k A I V p n => y.val colour) hx
    by_cases hp : p = 0
    · have hall (colour : Fin (n + 1) → Bool) :
          coefficientSplitAmbientToWord k A I V splitting colour
            (relativePositiveBarWordMap k A I V n x.val) = 0 := by
        by_cases hc : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hc⟩
        · have hgt : p < quotientEntryCount colour := by omega
          exact barStageToSplitWord_zero_of_quotient_count k A I splitting V p n colour hgt x
      have hw : relativePositiveBarWordMap k A I V n x.val = 0 := by
        have h := (coefficientSplitWord_reconstruct k A I V splitting
          (relativePositiveBarWordMap k A I V n x.val)).symm
        simpa only [hall, map_zero, Finset.sum_const_zero] using h
      have hx0 : x.val = 0 := (relativePositiveBarWordMap_injective k A I V n)
        (hw.trans (map_zero (relativePositiveBarWordMap k A I V n)).symm)
      change (barWordFiltration k A I V p n).subtype x ∈ barLowerFiltration k A I V p n
      rw [barLowerFiltration, ite_eq_left hp]
      simpa only [Submodule.mem_bot, Submodule.subtype_apply] using hx0
    · have hw : relativePositiveBarWordMap k A I V n x.val ∈
          coefficientIdealWordSpan k A I V (n + 1) (n + 1 - (p - 1)) := by
        rw [coefficientIdealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting V]
        change ∀ colour : Fin (n + 1) → Bool,
          splitWordIdealPositionCount colour < n + 1 - (p - 1) →
            coefficientSplitAmbientToWord k A I V splitting colour
              (relativePositiveBarWordMap k A I V n x.val) = 0
        intro colour hc
        by_cases hq : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hq⟩
        · have hcount := splitWordPositionCounts_add colour
          have hgt : p < quotientEntryCount colour := by omega
          exact barStageToSplitWord_zero_of_quotient_count k A I splitting V p n colour hgt x
      change (barWordFiltration k A I V p n).subtype x ∈ barLowerFiltration k A I V p n
      rw [barLowerFiltration, ite_eq_right hp]
      exact hw
  · intro hx
    change barStageToRelativeFixedGrade k A I splitting V p n x = 0
    apply Subtype.ext
    funext colour
    exact barLowerFiltration_le_ker_stageToSplitWord k A I splitting V p n colour.val colour.property hx

/-- Complete original positive layer extraction with its all-quotient coordinate zero. -/
def barLayerToRelativeFixedGrade (p n : ℕ) :
    barWordLayer k A I V p n →ₗ[k] barRelativeSplitWordGradeCoordinates k A I V p n :=
  (barLayerToSplitWordCoordinates k A I splitting V p n).codRestrict
    (barRelativeSplitWordGradeSpace k A I V p n) (fun z => by
      refine Submodule.Quotient.induction_on _ z ?_
      intro x colour hc
      change coefficientSplitAmbientToWord k A I V splitting colour.val
        (relativePositiveBarWordMap k A I V n x.val) = 0
      exact relativeBarWord_allQuotient_zero k A I splitting V n colour.val hc x.val)

private theorem barLayerToRelativeFixedGrade_projection (p n : ℕ)
    (x : barWordFiltration k A I V p n) :
    barLayerToRelativeFixedGrade k A I splitting V p n (barWordLayerProjection k A I V p n x) =
      barStageToRelativeFixedGrade k A I splitting V p n x := rfl

/-- The original positive native layer projection follows arbitrary-coefficient kernel reconstruction. -/
def barRelativeFixedGradeToLayer (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k] barWordLayer k A I V p n :=
  (barWordLayerProjection k A I V p n).comp (barFixedGradeToStage k A I splitting V p n)

/-- Actual original coefficient reconstruction recovers every complete fixed-p relative coordinate. -/
theorem barLayerToRelativeFixedGrade_comp_inverse (p n : ℕ) :
    (barLayerToRelativeFixedGrade k A I splitting V p n).comp
        (barRelativeFixedGradeToLayer k A I splitting V p n) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  change barLayerToRelativeFixedGrade k A I splitting V p n
    (barWordLayerProjection k A I V p n (barFixedGradeToStage k A I splitting V p n y)) = y
  rw [barLayerToRelativeFixedGrade_projection]
  exact barStageToRelativeFixedGrade_reconstruct k A I splitting V p n y

/-- The original positive layer is recovered from its complete coefficient coordinates. -/
theorem barRelativeFixedGradeToLayer_comp_extraction (p n : ℕ) :
    (barRelativeFixedGradeToLayer k A I splitting V p n).comp
        (barLayerToRelativeFixedGrade k A I splitting V p n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro x
  change barWordLayerProjection k A I V p n
      (barFixedGradeToStage k A I splitting V p n
        (barLayerToRelativeFixedGrade k A I splitting V p n (barWordLayerProjection k A I V p n x))) =
    barWordLayerProjection k A I V p n x
  rw [barLayerToRelativeFixedGrade_projection]
  have hzero : barStageToRelativeFixedGrade k A I splitting V p n
      (barFixedGradeToStage k A I splitting V p n
        (barStageToRelativeFixedGrade k A I splitting V p n x) - x) = 0 := by
    rw [map_sub, barStageToRelativeFixedGrade_reconstruct, sub_self]
  have hl : barFixedGradeToStage k A I splitting V p n
        (barStageToRelativeFixedGrade k A I splitting V p n x) - x ∈
      (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype := by
    rw [← barStageToRelativeFixedGrade_ker k A I splitting V p n]
    exact hzero
  exact (Submodule.Quotient.eq _).mpr hl

/-- The source splitting earns the original positive graded-term equivalence
with every relative source-count coefficient colour. -/
def barGradedSplitWordIso (p n : ℕ) :
    barWordLayer k A I V p n ≃ₗ[k] barRelativeSplitWordGradeCoordinates k A I V p n :=
  { barLayerToRelativeFixedGrade k A I splitting V p n with
    invFun := barRelativeFixedGradeToLayer k A I splitting V p n
    left_inv := fun x => congrArg (fun f => f x)
      (barRelativeFixedGradeToLayer_comp_extraction k A I splitting V p n)
    right_inv := fun y => congrArg (fun f => f y)
      (barLayerToRelativeFixedGrade_comp_inverse k A I splitting V p n) }

/-- The positive graded equivalence retains exactly the accepted complete arbitrary-coefficient extraction. -/
theorem barGradedSplitWordIso_apply (p n : ℕ) (z : barWordLayer k A I V p n) :
    (barGradedSplitWordIso k A I splitting V p n z).val =
      barLayerToSplitWordCoordinates k A I splitting V p n z := rfl

/-- Its inverse is precisely original-kernel reconstruction followed by the original bar quotient. -/
theorem barGradedSplitWordIso_symm_apply (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    (barGradedSplitWordIso k A I splitting V p n).symm y =
      barWordLayerProjection k A I V p n (barFixedGradeToStage k A I splitting V p n y) := rfl

section ExactBoundaries

private theorem quotientEntryCount_allTrue (N : ℕ) :
    quotientEntryCount (fun _ : Fin N => true) = N := by
  classical
  simp [quotientEntryCount]

private theorem sourceCountColour_allTrue {p N : ℕ} (hp : N ≤ p)
    (colour : splitWordGradeColours p N) : colour.val = fun _ => true := by
  classical
  have hcount := splitWordPositionCounts_add colour.val
  have hq := colour.property
  have hz : splitWordIdealPositionCount colour.val = 0 := by omega
  funext i
  cases hi : colour.val i
  · have hmem : i ∈ Finset.univ.filter (fun j : Fin N => colour.val j = false) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    change 0 < splitWordIdealPositionCount colour.val at hpos
    omega
  · rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Below the original word length, every original source-count naive colour is unrestricted. -/
theorem naiveRelativeSplitWordGradeSpace_eq_top (p n : ℕ) (hp : p < n + 1) :
    naiveRelativeSplitWordGradeSpace k A I p n = ⊤ := by
  apply top_unique
  intro y _ colour hc
  have hq := colour.property
  rw [hc, quotientEntryCount_allTrue] at hq
  omega

/-- Below the original word length, the original naive layer is equivalent to the full fixed-p family. -/
def naiveGradedSplitWordFullIso (p n : ℕ) (hp : p < n + 1) :
    naiveWordLayer k A I p n ≃ₗ[k] naiveSplitWordGradeCoordinates k A I p n :=
  (naiveGradedSplitWordIso k A I splitting p n).trans
    (LinearEquiv.ofTop (naiveRelativeSplitWordGradeSpace k A I p n)
      (naiveRelativeSplitWordGradeSpace_eq_top k A I p n hp))

/-- The full-family equivalence keeps exactly the original accepted naive extraction. -/
theorem naiveGradedSplitWordFullIso_apply (p n : ℕ) (hp : p < n + 1)
    (z : naiveWordLayer k A I p n) :
    naiveGradedSplitWordFullIso k A I splitting p n hp z =
      naiveLayerToSplitWordCoordinates k A I splitting p n z := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- At and beyond word length, the relative source-count naive coordinate module is zero. -/
theorem naiveRelativeSplitWordGrade_eq_zero (p n : ℕ) (hp : n + 1 ≤ p)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) : y = 0 := by
  apply Subtype.ext
  funext colour
  exact y.property colour (sourceCountColour_allTrue hp colour)

include splitting in
/-- At and beyond word length, the original naive graded layer is zero. -/
theorem naiveWordLayer_eq_zero_of_wordLength_le (p n : ℕ) (hp : n + 1 ≤ p)
    (z : naiveWordLayer k A I p n) : z = 0 := by
  apply (naiveGradedSplitWordIso k A I splitting p n).injective
  exact (naiveRelativeSplitWordGrade_eq_zero k A I p n hp
    (naiveGradedSplitWordIso k A I splitting p n z)).trans (map_zero _).symm

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Below word length every original fixed-p coefficient colour remains unrestricted. -/
theorem barRelativeSplitWordGradeSpace_eq_top (p n : ℕ) (hp : p < n + 1) :
    barRelativeSplitWordGradeSpace k A I V p n = ⊤ := by
  apply top_unique
  intro y _ colour hc
  have hq := colour.property
  rw [hc, quotientEntryCount_allTrue] at hq
  omega

/-- Below word length the original positive layer is equivalent to the full coefficient family. -/
def barGradedSplitWordFullIso (p n : ℕ) (hp : p < n + 1) :
    barWordLayer k A I V p n ≃ₗ[k] barSplitWordGradeCoordinates k A I V p n :=
  (barGradedSplitWordIso k A I splitting V p n).trans
    (LinearEquiv.ofTop (barRelativeSplitWordGradeSpace k A I V p n)
      (barRelativeSplitWordGradeSpace_eq_top k A I V p n hp))

/-- The full coefficient-family equivalence is the exact original accepted bar extraction. -/
theorem barGradedSplitWordFullIso_apply (p n : ℕ) (hp : p < n + 1)
    (z : barWordLayer k A I V p n) :
    barGradedSplitWordFullIso k A I splitting V p n hp z =
      barLayerToSplitWordCoordinates k A I splitting V p n z := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- At and beyond word length the positive relative coordinate family is zero. -/
theorem barRelativeSplitWordGrade_eq_zero (p n : ℕ) (hp : n + 1 ≤ p)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) : y = 0 := by
  apply Subtype.ext
  funext colour
  exact y.property colour (sourceCountColour_allTrue hp colour)

include splitting in
/-- At and beyond word length the original positive graded layer is zero. -/
theorem barWordLayer_eq_zero_of_wordLength_le (p n : ℕ) (hp : n + 1 ≤ p)
    (z : barWordLayer k A I V p n) : z = 0 := by
  apply (barGradedSplitWordIso k A I splitting V p n).injective
  exact (barRelativeSplitWordGrade_eq_zero k A I V p n hp
    (barGradedSplitWordIso k A I splitting V p n z)).trans (map_zero _).symm

/-- The exact original naive associated-complex term inherits this native graded coordinate equivalence. -/
def naiveAssociatedGradedSplitWordIso (p n : ℕ) :
    (naiveAssociatedWordComplex k A I p).X n ≅
      ModuleCat.of k (naiveRelativeSplitWordGradeCoordinates k A I p n) :=
  (naiveGradedSplitWordIso k A I splitting p n).toModuleIso

/-- The exact original positive associated-complex term retains source degree n+1 and arbitrary V. -/
def barAssociatedGradedSplitWordIso (p n : ℕ) :
    (barAssociatedWordComplex k A I V p).X (n + 1) ≅
      ModuleCat.of k (barRelativeSplitWordGradeCoordinates k A I V p n) :=
  (barGradedSplitWordIso k A I splitting V p n).toModuleIso


end ExactBoundaries

end ModuleCat.Algebra.Hochschild.NonUnital
