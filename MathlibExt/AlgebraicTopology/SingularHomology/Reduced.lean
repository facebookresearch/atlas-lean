/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import MathlibExt.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Integral and reduced singular homology

We define the integral singular homology functor `Hₙ(-; ℤ)` as the
Mathlib homology functor evaluated at `ℤ`, prove the dimension axiom,
define the augmentation and reduced homology, show `H̃ₙ ≅ Hₙ` for `n≠0`,
and that contractible spaces have `Hₙ=0` and `H₀≅ℤ`.  We also define the
integral singular chain functor.

## Main definitions
* `pointSingularHomologyFunctor`
* `singularHomologyAugmentation`
* `reducedSingularHomologyFunctor`
* `reducedSingularHomology`
* `reducedSingularHomologyι`
* `reducedSingularHomologyObjIso`
* `singularHomologyPUnitZeroIso`
* `reducedSingularHomologyFunctorIso`
* `reducedSingularHomologyShortComplex`
* `reducedSingularHomologySplitting`
* `singularHomologyIsoReducedBiprod`
* `reducedSingularHomology_map_eq_of_homotopy`
* `reducedSingularHomologyMapIso`
* `reducedSingularHomologyMapIso_hom`
* `reducedSingularHomologyMapIso_inv`
* `singularHomologyℤFunctor`
* `singularHomologyℤ`
* `singularHomologyℤAugmentation`
* `reducedSingularHomologyℤ`
* `reducedSingularHomologyℤObjIso`
* `singularHomologyℤMapIso`
* `singularChainℤFunctor`
* `singularChainℤMap`

## Main results
* `isZero_singularHomology_punit`
* `isZero_reducedSingularHomology_punit`
* `isZero_singularHomologyℤ_punit`
* `singularHomologyℤPUnitZeroIso`
* `reducedSingularHomologyℤIso`
* `singularHomologyℤIsoReducedBiprod`
* `isZero_singularHomologyℤ_of_contractible`
* `singularHomologyℤContractibleZeroIso`
* `reducedSingularHomology_map_eq_of_homotopy`
* `reducedSingularHomologyMapIso`

## References
* Hatcher, *Algebraic Topology*
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory Simplicial SimplexCategory SimplicialObject Matrix Limits Opposite

namespace AlgebraicTopology

universe w v u

section ReducedFunctor

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The constant functor at the `n`th singular homology of a point with coefficients in `R`. -/
noncomputable def pointSingularHomologyFunctor (R : C) (n : ℕ) : TopCat.{w} ⥤ C where
  obj _ := ((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation induced by the unique map from each space to a point. -/
noncomputable def singularHomologyAugmentation (R : C) (n : ℕ) :
    (singularHomologyFunctor C n).obj R ⟶ pointSingularHomologyFunctor C R n where
  app X := ((singularHomologyFunctor C n).obj R).map (TopCat.isTerminalPUnit.from X)
  naturality X Y f := by
    have h : ((singularHomologyFunctor C n).obj R).map f ≫
        ((singularHomologyFunctor C n).obj R).map (TopCat.isTerminalPUnit.from Y) =
          ((singularHomologyFunctor C n).obj R).map (TopCat.isTerminalPUnit.from X) := by
      rw [← Functor.map_comp]
      exact congrArg ((singularHomologyFunctor C n).obj R).map
        (TopCat.isTerminalPUnit.hom_ext _ _)
    simpa only [pointSingularHomologyFunctor, Category.comp_id] using h

/-- Reduced singular homology as the kernel of the augmentation in the functor category. -/
noncomputable def reducedSingularHomologyFunctor (R : C) (n : ℕ) : TopCat.{w} ⥤ C :=
  kernel (singularHomologyAugmentation C R n)

/-- Reduced singular homology of a space. -/
noncomputable abbrev reducedSingularHomology (R : C) (n : ℕ) (X : TopCat.{w}) : C :=
  (reducedSingularHomologyFunctor C R n).obj X

/-- The natural inclusion from reduced to ordinary singular homology. -/
noncomputable abbrev reducedSingularHomologyι (R : C) (n : ℕ) :
    reducedSingularHomologyFunctor C R n ⟶ (singularHomologyFunctor C n).obj R :=
  kernel.ι (singularHomologyAugmentation C R n)

@[reassoc (attr := simp)]
lemma reducedSingularHomologyι_comp_augmentation (R : C) (n : ℕ) :
    reducedSingularHomologyι C R n ≫ singularHomologyAugmentation C R n = 0 :=
  kernel.condition _

/-- Evaluation computes the functor-category kernel as the kernel of the component augmentation. -/
noncomputable def reducedSingularHomologyObjIso (R : C) (n : ℕ) (X : TopCat.{w}) :
    reducedSingularHomology C R n X ≅
      kernel ((singularHomologyAugmentation C R n).app X) :=
  PreservesKernel.iso ((evaluation TopCat.{w} C).obj X)
    (singularHomologyAugmentation C R n)

@[reassoc]
lemma reducedSingularHomologyObjIso_hom_ι (R : C) (n : ℕ) (X : TopCat.{w}) :
    (reducedSingularHomologyObjIso C R n X).hom ≫
        kernel.ι ((singularHomologyAugmentation C R n).app X) =
      (reducedSingularHomologyι C R n).app X := by
  rw [← cancel_epi (reducedSingularHomologyObjIso C R n X).inv]
  simp only [Iso.inv_hom_id_assoc]
  change kernel.ι (((evaluation TopCat.{w} C).obj X).map
      (singularHomologyAugmentation C R n)) =
    (PreservesKernel.iso ((evaluation TopCat.{w} C).obj X)
        (singularHomologyAugmentation C R n)).inv ≫
      ((evaluation TopCat.{w} C).obj X).map
        (kernel.ι (singularHomologyAugmentation C R n))
  exact (PreservesKernel.iso_inv_ι ((evaluation TopCat.{w} C).obj X)
    (singularHomologyAugmentation C R n)).symm

/-- Zeroth singular homology of a point is canonically the coefficient object. -/
noncomputable def singularHomologyPUnitZeroIso (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of PUnit) ≅ R :=
  asIso ((TopCat.of PUnit).singularHomology₀ε R)

@[reassoc (attr := simp)]
lemma singularHomologyPUnitZeroIso_hom (R : C) :
    (singularHomologyPUnitZeroIso C R).hom = (TopCat.of PUnit).singularHomology₀ε R :=
  rfl

@[reassoc]
theorem singularHomologyAugmentation_app_comp_singularHomology₀ε (R : C) (X : TopCat.{w}) :
    (singularHomologyAugmentation C R 0).app X ≫ (TopCat.of PUnit).singularHomology₀ε R =
      X.singularHomology₀ε R := by
  dsimp only [singularHomologyAugmentation]
  exact TopCat.singularHomologyMap_comp_singularHomology₀ε (TopCat.isTerminalPUnit.from X) R

/-- Canonical comparison: reduced `H₀` is the kernel of the canonical augmentation `H₀ → R`. -/
noncomputable def reducedSingularHomologyZeroCanonicalKernelIso (R : C) (X : TopCat.{w}) :
    reducedSingularHomology C R 0 X ≅ kernel (X.singularHomology₀ε R) := by
  let f := (singularHomologyAugmentation C R 0).app X
  let g : (pointSingularHomologyFunctor C R 0).obj X ⟶ R :=
    (TopCat.of PUnit).singularHomology₀ε R
  let ι := (reducedSingularHomologyι C R 0).app X
  have hgIso : IsIso g := by
    change IsIso ((TopCat.of PUnit).singularHomology₀ε R)
    infer_instance
  have hgMono : Mono g := by
    have := hgIso
    infer_instance
  have hι : ι ≫ f = 0 := by
    change (reducedSingularHomologyι C R 0).app X ≫ (singularHomologyAugmentation C R 0).app X = 0
    exact NatTrans.congr_app (reducedSingularHomologyι_comp_augmentation C R 0) X
  let fork : KernelFork f := KernelFork.ofι ι hι
  have hFork : IsLimit fork :=
    kernel.isoKernel (l := ι) (i := reducedSingularHomologyObjIso C R 0 X)
      (h := reducedSingularHomologyObjIso_hom_ι C R 0 X)
  have hEq : X.singularHomology₀ε R = f ≫ g :=
    (singularHomologyAugmentation_app_comp_singularHomology₀ε C R X).symm
  haveI := hgMono
  have hForkComp := isKernelCompMono hFork g hEq
  exact IsLimit.conePointUniqueUpToIso hForkComp (limit.isLimit _)

@[reassoc (attr := simp)]
lemma reducedSingularHomologyZeroCanonicalKernelIso_hom_ι (R : C) (X : TopCat.{w}) :
    (reducedSingularHomologyZeroCanonicalKernelIso C R X).hom ≫
      kernel.ι (X.singularHomology₀ε R) =
        (reducedSingularHomologyι C R 0).app X := by
  let f := (singularHomologyAugmentation C R 0).app X
  let g : (pointSingularHomologyFunctor C R 0).obj X ⟶ R :=
    (TopCat.of PUnit).singularHomology₀ε R
  let ι := (reducedSingularHomologyι C R 0).app X
  have hgIso : IsIso g := by
    change IsIso ((TopCat.of PUnit).singularHomology₀ε R)
    infer_instance
  have hgMono : Mono g := by
    have := hgIso
    infer_instance
  have hι : ι ≫ f = 0 := by
    change (reducedSingularHomologyι C R 0).app X ≫ (singularHomologyAugmentation C R 0).app X = 0
    exact NatTrans.congr_app (reducedSingularHomologyι_comp_augmentation C R 0) X
  let fork : KernelFork f := KernelFork.ofι ι hι
  have hFork : IsLimit fork :=
    kernel.isoKernel (l := ι) (i := reducedSingularHomologyObjIso C R 0 X)
      (h := reducedSingularHomologyObjIso_hom_ι C R 0 X)
  have hEq : X.singularHomology₀ε R = f ≫ g :=
    (singularHomologyAugmentation_app_comp_singularHomology₀ε C R X).symm
  have := hgMono
  have hForkComp := isKernelCompMono hFork g hEq
  change (IsLimit.conePointUniqueUpToIso hForkComp (limit.isLimit _)).hom ≫
      kernel.ι (X.singularHomology₀ε R) = (reducedSingularHomologyι C R 0).app X
  exact IsLimit.conePointUniqueUpToIso_hom_comp hForkComp (limit.isLimit _) WalkingParallelPair.zero

instance isIso_singularHomologyAugmentationAppZero_of_pathConnectedSpace
    (R : C) (X : TopCat.{w}) [PathConnectedSpace X] :
    IsIso ((singularHomologyAugmentation C R 0).app X) := by
  have : IsIso (X.singularHomology₀ε R) := inferInstance
  let g : (pointSingularHomologyFunctor C R 0).obj X ⟶ R :=
    (TopCat.of PUnit).singularHomology₀ε R
  have hgIso : IsIso g := by
    change IsIso ((TopCat.of PUnit).singularHomology₀ε R)
    infer_instance
  have h_fg : (singularHomologyAugmentation C R 0).app X ≫ g =
      X.singularHomology₀ε R :=
    singularHomologyAugmentation_app_comp_singularHomology₀ε C R X
  have h_eq : (singularHomologyAugmentation C R 0).app X =
      X.singularHomology₀ε R ≫ inv g := by
    have := hgIso
    calc (singularHomologyAugmentation C R 0).app X
        = (singularHomologyAugmentation C R 0).app X ≫ 𝟙 _ := by
          rw [Category.comp_id]
      _ = (singularHomologyAugmentation C R 0).app X ≫ (g ≫ inv g) := by
          rw [IsIso.hom_inv_id]
      _ = ((singularHomologyAugmentation C R 0).app X ≫ g) ≫ inv g := by
          rw [Category.assoc]
      _ = X.singularHomology₀ε R ≫ inv g := by rw [h_fg]
  have := hgIso
  rw [h_eq]
  infer_instance

theorem isZero_reducedSingularHomologyZero_of_pathConnectedSpace
    (R : C) (X : TopCat.{w}) [PathConnectedSpace X] :
    IsZero (reducedSingularHomology C R 0 X) := by
  have : IsIso ((singularHomologyAugmentation C R 0).app X) := inferInstance
  have hker : IsZero (kernel ((singularHomologyAugmentation C R 0).app X)) :=
    isZero_kernel_of_mono ((singularHomologyAugmentation C R 0).app X)
  exact hker.of_iso (reducedSingularHomologyObjIso C R 0 X)

theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map f = ((singularHomologyFunctor C n).obj R).map g :=
  H.congr_homologyMap_singularChainComplexFunctor R n

/-- Homotopy-inverse maps `f` and `g` induce inverse maps on degree-`n`
singular homology with coefficient object `R`. -/
noncomputable def singularHomologyMapIso (n : ℕ) {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X)) (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (R : C) :
    ((singularHomologyFunctor C n).obj R).obj X ≅ ((singularHomologyFunctor C n).obj R).obj Y where
  hom := ((singularHomologyFunctor C n).obj R).map f
  inv := ((singularHomologyFunctor C n).obj R).map g
  hom_inv_id := by
    have hfg_eq : ((singularHomologyFunctor C n).obj R).map (f ≫ g) =
        ((singularHomologyFunctor C n).obj R).map (𝟙 X) :=
      singularHomology_map_eq_of_homotopy C hfg R n
    calc ((singularHomologyFunctor C n).obj R).map f ≫ ((singularHomologyFunctor C n).obj R).map g
        = ((singularHomologyFunctor C n).obj R).map (f ≫ g) := by
          rw [← ((singularHomologyFunctor C n).obj R).map_comp]
      _ = ((singularHomologyFunctor C n).obj R).map (𝟙 X) := hfg_eq
      _ = 𝟙 _ := by rw [((singularHomologyFunctor C n).obj R).map_id]
  inv_hom_id := by
    have hgf_eq : ((singularHomologyFunctor C n).obj R).map (g ≫ f) =
        ((singularHomologyFunctor C n).obj R).map (𝟙 Y) :=
      singularHomology_map_eq_of_homotopy C hgf R n
    calc ((singularHomologyFunctor C n).obj R).map g ≫ ((singularHomologyFunctor C n).obj R).map f
        = ((singularHomologyFunctor C n).obj R).map (g ≫ f) := by
          rw [← ((singularHomologyFunctor C n).obj R).map_comp]
      _ = ((singularHomologyFunctor C n).obj R).map (𝟙 Y) := hgf_eq
      _ = 𝟙 _ := by rw [((singularHomologyFunctor C n).obj R).map_id]

@[simp]
theorem singularHomologyMapIso_hom (n : ℕ) {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X)) (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (R : C) :
    (singularHomologyMapIso C n f g hfg hgf R).hom =
      ((singularHomologyFunctor C n).obj R).map f := rfl

@[simp]
theorem singularHomologyMapIso_inv (n : ℕ) {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X)) (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (R : C) :
    (singularHomologyMapIso C n f g hfg hgf R).inv =
      ((singularHomologyFunctor C n).obj R).map g := rfl

theorem reducedSingularHomology_map_eq_of_homotopy
    {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    (reducedSingularHomologyFunctor C R n).map f =
      (reducedSingularHomologyFunctor C R n).map g := by
  have : Mono (kernel.ι ((singularHomologyAugmentation C R n).app Y)) := inferInstance
  have : Mono (reducedSingularHomologyObjIso C R n Y).hom := inferInstance
  have : Mono ((reducedSingularHomologyι C R n).app Y) := by
    rw [(reducedSingularHomologyObjIso_hom_ι C R n Y).symm]
    infer_instance
  apply (cancel_mono ((reducedSingularHomologyι C R n).app Y)).mp
  calc (reducedSingularHomologyFunctor C R n).map f ≫
          (reducedSingularHomologyι C R n).app Y
      = (reducedSingularHomologyι C R n).app X ≫
          ((singularHomologyFunctor C n).obj R).map f :=
        (reducedSingularHomologyι C R n).naturality f
    _ = (reducedSingularHomologyι C R n).app X ≫
          ((singularHomologyFunctor C n).obj R).map g := by
        rw [singularHomology_map_eq_of_homotopy C H R n]
    _ = (reducedSingularHomologyFunctor C R n).map g ≫
          (reducedSingularHomologyι C R n).app Y :=
        ((reducedSingularHomologyι C R n).naturality g).symm

/-- Homotopy-inverse maps `f` and `g` induce inverse maps on degree-`n`
reduced singular homology with coefficient object `R`. -/
noncomputable def reducedSingularHomologyMapIso (n : ℕ)
    {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (R : C) :
    reducedSingularHomology C R n X ≅ reducedSingularHomology C R n Y where
  hom := (reducedSingularHomologyFunctor C R n).map f
  inv := (reducedSingularHomologyFunctor C R n).map g
  hom_inv_id := by
    have hfg_eq : (reducedSingularHomologyFunctor C R n).map (f ≫ g) =
        (reducedSingularHomologyFunctor C R n).map (𝟙 X) :=
      reducedSingularHomology_map_eq_of_homotopy C hfg R n
    calc (reducedSingularHomologyFunctor C R n).map f ≫
            (reducedSingularHomologyFunctor C R n).map g
        = (reducedSingularHomologyFunctor C R n).map (f ≫ g) := by
          rw [← (reducedSingularHomologyFunctor C R n).map_comp]
      _ = (reducedSingularHomologyFunctor C R n).map (𝟙 X) := hfg_eq
      _ = 𝟙 _ := by rw [(reducedSingularHomologyFunctor C R n).map_id]
  inv_hom_id := by
    have hgf_eq : (reducedSingularHomologyFunctor C R n).map (g ≫ f) =
        (reducedSingularHomologyFunctor C R n).map (𝟙 Y) :=
      reducedSingularHomology_map_eq_of_homotopy C hgf R n
    calc (reducedSingularHomologyFunctor C R n).map g ≫
            (reducedSingularHomologyFunctor C R n).map f
        = (reducedSingularHomologyFunctor C R n).map (g ≫ f) := by
          rw [← (reducedSingularHomologyFunctor C R n).map_comp]
      _ = (reducedSingularHomologyFunctor C R n).map (𝟙 Y) := hgf_eq
      _ = 𝟙 _ := by rw [(reducedSingularHomologyFunctor C R n).map_id]

@[simp]
theorem reducedSingularHomologyMapIso_hom (n : ℕ)
    {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (R : C) :
    (reducedSingularHomologyMapIso C n f g hfg hgf R).hom =
      (reducedSingularHomologyFunctor C R n).map f := rfl

@[simp]
theorem reducedSingularHomologyMapIso_inv (n : ℕ)
    {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (R : C) :
    (reducedSingularHomologyMapIso C n f g hfg hgf R).inv =
      (reducedSingularHomologyFunctor C R n).map g := rfl

/-- Positive-degree singular homology of a point vanishes. -/
lemma isZero_singularHomology_punit (R : C) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R (TopCat.of PUnit) hn

/-- In positive degrees, the augmentation is the zero natural transformation. -/
lemma singularHomologyAugmentation_eq_zero (R : C) (n : ℕ) (hn : n ≠ 0) :
    singularHomologyAugmentation C R n = 0 := by
  apply NatTrans.ext
  funext X
  exact (isZero_singularHomology_punit C R n hn).eq_zero_of_tgt _

/-- In positive degrees, reduced and ordinary singular homology are naturally isomorphic. -/
noncomputable def reducedSingularHomologyFunctorIso (R : C) (n : ℕ) (hn : n ≠ 0) :
    reducedSingularHomologyFunctor C R n ≅ (singularHomologyFunctor C n).obj R :=
  kernelIsoOfEq (singularHomologyAugmentation_eq_zero C R n hn) ≪≫ kernelZeroIsoSource

@[simp]
lemma reducedSingularHomologyFunctorIso_hom (R : C) (n : ℕ) (hn : n ≠ 0) :
    (reducedSingularHomologyFunctorIso C R n hn).hom =
      reducedSingularHomologyι C R n := by
  change (kernelIsoOfEq (singularHomologyAugmentation_eq_zero C R n hn)).hom ≫
      kernel.ι (0 : (singularHomologyFunctor C n).obj R ⟶
        pointSingularHomologyFunctor C R n) =
    kernel.ι (singularHomologyAugmentation C R n)
  exact kernelIsoOfEq_hom_comp_ι _

/-- Reduced singular homology of a point vanishes in every degree. -/
theorem isZero_reducedSingularHomology_punit (R : C) (n : ℕ) :
    IsZero (reducedSingularHomology C R n (TopCat.of PUnit)) := by
  have : IsIso ((singularHomologyAugmentation C R n).app (TopCat.of PUnit)) := by
    change IsIso (((singularHomologyFunctor C n).obj R).map
      (TopCat.isTerminalPUnit.from (TopCat.of PUnit)))
    rw [TopCat.isTerminalPUnit.hom_ext
      (TopCat.isTerminalPUnit.from (TopCat.of PUnit)) (𝟙 _)]
    infer_instance
  have hker : IsZero (kernel
      ((singularHomologyAugmentation C R n).app (TopCat.of PUnit))) :=
    (isZero_zero C).of_iso
      (kernel.ofMono ((singularHomologyAugmentation C R n).app (TopCat.of PUnit)))
  exact hker.of_iso
    (reducedSingularHomologyObjIso C R n (TopCat.of PUnit))

theorem isZero_singularHomology_of_contractible (R : C) (n : ℕ) (hn : n ≠ 0)
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv (X := X) (Y := PUnit)
  have iso : ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit) :=
    singularHomologyMapIso C n (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
      e.left_inv.some e.right_inv.some R
  exact (isZero_singularHomology_punit C R n hn).of_iso iso

/-- The augmentation `Hₙ(X) → Hₙ(point)` is an iso when `X` is contractible. -/
instance isIso_singularHomologyAugmentationApp_of_contractibleSpace
    (R : C) (n : ℕ) (X : TopCat.{w}) [ContractibleSpace X] :
    IsIso ((singularHomologyAugmentation C R n).app X) := by
  by_cases hn0 : n = 0
  · subst hn0
    have : PathConnectedSpace X := inferInstance
    infer_instance
  · have hn : n ≠ 0 := hn0
    have hX : IsZero (((singularHomologyFunctor C n).obj R).obj X) :=
      isZero_singularHomology_of_contractible C R n hn ↥X
    have hY : IsZero
        (((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)) :=
      isZero_singularHomology_punit C R n hn
    exact IsZero.isIso hX hY ((singularHomologyAugmentation C R n).app X)

/-- For a map `f : A ⟶ X` with contractible target `X`, reduced homology of `A`
is the kernel of the induced map on ordinary singular homology.
It starts with `reducedSingularHomologyObjIso`, rewrites the augmentation at `A`
as `Hₙ(f) ≫ augmentation at X` by naturality of `singularHomologyAugmentation`
(`pointSingularHomologyFunctor` is trivial on maps), uses `kernelIsoOfEq` for
that equality, then removes the augmentation at `X` via `kernelCompMono`
since the contractible instance makes it an iso hence mono. -/
noncomputable def reducedSingularHomologyKernelIsoOfContractibleTarget (R : C) (n : ℕ)
    {A X : TopCat.{w}} (f : A ⟶ X) [ContractibleSpace X] :
    reducedSingularHomology C R n A ≅
      kernel (((singularHomologyFunctor C n).obj R).map f) := by
  let p := ((singularHomologyFunctor C n).obj R).map f
  let g := (singularHomologyAugmentation C R n).app X
  let h := (singularHomologyAugmentation C R n).app A
  let ι := (reducedSingularHomologyι C R n).app A
  have hgIso : IsIso g := inferInstance
  have hgMono : Mono g := by
    have := hgIso
    infer_instance
  have hι : ι ≫ h = 0 := by
    change (reducedSingularHomologyι C R n).app A ≫ (singularHomologyAugmentation C R n).app A = 0
    exact NatTrans.congr_app (reducedSingularHomologyι_comp_augmentation C R n) A
  let fork : KernelFork h := KernelFork.ofι ι hι
  have hFork : IsLimit fork :=
    kernel.isoKernel (l := ι) (i := reducedSingularHomologyObjIso C R n A)
      (h := reducedSingularHomologyObjIso_hom_ι C R n A)
  have hpg : p ≫ g = h := by
    have hNat := (singularHomologyAugmentation C R n).naturality f
    simp only [pointSingularHomologyFunctor, Category.comp_id] at hNat
    exact hNat
  have hZero : ι ≫ p = 0 := by
    have := hgMono
    have ha : (ι ≫ p) ≫ g = ι ≫ (p ≫ g) := by rw [Category.assoc]
    have hb : ι ≫ (p ≫ g) = ι ≫ h := congrArg (fun t => ι ≫ t) hpg
    have hc : (ι ≫ p) ≫ g = 0 := ha.trans (hb.trans hι)
    have hd : (ι ≫ p) ≫ g = 0 ≫ g := hc.trans (zero_comp).symm
    exact (cancel_mono g).mp hd
  have hForkP : IsLimit (KernelFork.ofι ι hZero) :=
    isKernelOfComp g h hFork hZero hpg
  exact IsLimit.conePointUniqueUpToIso hForkP (limit.isLimit _)

/-- For a map `f : A ⟶ X` with contractible target `X`, the forward map of
`reducedSingularHomologyKernelIsoOfContractibleTarget` followed by the kernel
inclusion of `Hₙ(f)` equals the reduced homology inclusion
`(reducedSingularHomologyι C R n).app A`. -/
@[reassoc (attr := simp)]
theorem reducedSingularHomologyKernelIsoOfContractibleTarget_hom_ι (R : C) (n : ℕ)
    {A X : TopCat.{w}} (f : A ⟶ X) [ContractibleSpace X] :
    (reducedSingularHomologyKernelIsoOfContractibleTarget C R n f).hom ≫
      kernel.ι (((singularHomologyFunctor C n).obj R).map f) =
      (reducedSingularHomologyι C R n).app A := by
  let p := ((singularHomologyFunctor C n).obj R).map f
  let g := (singularHomologyAugmentation C R n).app X
  let h := (singularHomologyAugmentation C R n).app A
  let ι := (reducedSingularHomologyι C R n).app A
  have hgIso : IsIso g := inferInstance
  have hgMono : Mono g := by
    have := hgIso
    infer_instance
  have hι : ι ≫ h = 0 := by
    change (reducedSingularHomologyι C R n).app A ≫ (singularHomologyAugmentation C R n).app A = 0
    exact NatTrans.congr_app (reducedSingularHomologyι_comp_augmentation C R n) A
  let fork : KernelFork h := KernelFork.ofι ι hι
  have hFork : IsLimit fork :=
    kernel.isoKernel (l := ι) (i := reducedSingularHomologyObjIso C R n A)
      (h := reducedSingularHomologyObjIso_hom_ι C R n A)
  have hpg : p ≫ g = h := by
    have hNat := (singularHomologyAugmentation C R n).naturality f
    simp only [pointSingularHomologyFunctor, Category.comp_id] at hNat
    exact hNat
  have hZero : ι ≫ p = 0 := by
    have := hgMono
    have ha : (ι ≫ p) ≫ g = ι ≫ (p ≫ g) := by rw [Category.assoc]
    have hb : ι ≫ (p ≫ g) = ι ≫ h := congrArg (fun t => ι ≫ t) hpg
    have hc : (ι ≫ p) ≫ g = 0 := ha.trans (hb.trans hι)
    have hd : (ι ≫ p) ≫ g = 0 ≫ g := hc.trans zero_comp.symm
    exact (cancel_mono g).mp hd
  have hForkP : IsLimit (KernelFork.ofι ι hZero) :=
    isKernelOfComp g h hFork hZero hpg
  change (IsLimit.conePointUniqueUpToIso hForkP (limit.isLimit _)).hom ≫ kernel.ι p = ι
  exact IsLimit.conePointUniqueUpToIso_hom_comp hForkP (limit.isLimit _) WalkingParallelPair.zero

/-- The degree-zero singular-homology augmentation of a contractible space is
an isomorphism to its coefficient object `R`. -/
noncomputable def singularHomologyZeroIso_of_contractible (R : C) (X : Type w)
    [TopologicalSpace X] [ContractibleSpace X] :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of X) ≅ R :=
  asIso ((TopCat.of X).singularHomology₀ε R)

theorem isZero_reducedSingularHomology_of_contractible (R : C) (n : ℕ)
    (X : Type w) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (reducedSingularHomology C R n (TopCat.of X)) := by
  by_cases hn0 : n = 0
  · subst hn0
    have : PathConnectedSpace (TopCat.of X) := inferInstance
    exact isZero_reducedSingularHomologyZero_of_pathConnectedSpace C R (TopCat.of X)
  · have hn : n ≠ 0 := hn0
    have hOrd : IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of X)) :=
      isZero_singularHomology_of_contractible C R n hn X
    have iso : reducedSingularHomology C R n (TopCat.of X) ≅
        ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) :=
      (reducedSingularHomologyFunctorIso C R n hn).app (TopCat.of X)
    exact hOrd.of_iso iso

/-- The functorial kernel sequence defining reduced homology. -/
noncomputable def reducedSingularHomologyShortComplex (R : C) (n : ℕ) :
    ShortComplex (TopCat.{w} ⥤ C) :=
  ShortComplex.mk (reducedSingularHomologyι C R n)
    (singularHomologyAugmentation C R n)
    (reducedSingularHomologyι_comp_augmentation C R n)

lemma reducedSingularHomologyShortComplex_exact (R : C) (n : ℕ) :
    (reducedSingularHomologyShortComplex C R n).Exact := by
  change (ShortComplex.mk (kernel.ι (singularHomologyAugmentation C R n))
    (singularHomologyAugmentation C R n) (kernel.condition _)).Exact
  exact ShortComplex.exact_kernel (singularHomologyAugmentation C R n)

/-- The reduced-homology kernel sequence evaluated at a space. -/
noncomputable def reducedSingularHomologyShortComplexObj (R : C) (n : ℕ) (X : TopCat.{w}) :
    ShortComplex C :=
  (reducedSingularHomologyShortComplex C R n).map ((evaluation TopCat.{w} C).obj X)

lemma reducedSingularHomologyShortComplexObj_exact (R : C) (n : ℕ) (X : TopCat.{w}) :
    (reducedSingularHomologyShortComplexObj C R n X).Exact :=
  (reducedSingularHomologyShortComplex_exact C R n).map
    ((evaluation TopCat.{w} C).obj X)

/-- A point of `X` splits the reduced-homology kernel sequence. -/
noncomputable def reducedSingularHomologySplitting (R : C) (n : ℕ) {X : TopCat.{w}}
    (b : TopCat.of PUnit ⟶ X) :
    (reducedSingularHomologyShortComplexObj C R n X).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    (reducedSingularHomologyShortComplexObj_exact C R n X)
    (((singularHomologyFunctor C n).obj R).map b)
    (by
      change ((singularHomologyFunctor C n).obj R).map b ≫
        ((singularHomologyFunctor C n).obj R).map
          (TopCat.isTerminalPUnit.from X) = 𝟙 _
      rw [← Functor.map_comp,
        TopCat.isTerminalPUnit.hom_ext (b ≫ _) (𝟙 _)]
      exact ((singularHomologyFunctor C n).obj R).map_id _)
    (by
      change Mono ((reducedSingularHomologyι C R n).app X)
      rw [← reducedSingularHomologyObjIso_hom_ι]
      infer_instance)

/-- For a pointed space, ordinary homology splits into reduced homology and point homology. -/
noncomputable def singularHomologyIsoReducedBiprod (R : C) (n : ℕ) {X : TopCat.{w}}
    (b : TopCat.of PUnit ⟶ X) :
    ((singularHomologyFunctor C n).obj R).obj X ≅
      reducedSingularHomology C R n X ⊞
        ((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit) :=
  (reducedSingularHomologySplitting C R n b).isoBinaryBiproduct

end ReducedFunctor

/-- The `n`-th integral singular homology functor `TopCat ⥤ Ab`. -/
noncomputable def singularHomologyℤFunctor (n : ℕ) : TopCat.{0} ⥤ AddCommGrpCat.{0} :=
  (singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)

/-- Integral singular homology `Hₙ(X; ℤ)` as an abelian group. -/
noncomputable abbrev singularHomologyℤ (n : ℕ) (X : TopCat.{0}) : AddCommGrpCat.{0} :=
  (singularHomologyℤFunctor n).obj X

/-- Higher integral homology of a totally disconnected space vanishes. -/
theorem isZero_singularHomologyℤ_of_totallyDisconnectedSpace (n : ℕ) (hn : n ≠ 0)
    (X : TopCat.{0}) [TotallyDisconnectedSpace X] : IsZero (singularHomologyℤ n X) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace AddCommGrpCat.{0} n
    (AddCommGrpCat.of ℤ) X hn

/-- Dimension axiom (vanishing part): `Hₙ(point; ℤ) = 0` for `n ≠ 0`. -/
theorem isZero_singularHomologyℤ_punit (n : ℕ) (hn : n ≠ 0) :
    IsZero (singularHomologyℤ n (TopCat.of PUnit)) :=
  isZero_singularHomology_punit AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n hn

/-- Dimension axiom (degree-zero part): `H₀(point; ℤ) ≅ ℤ`. -/
noncomputable def singularHomologyℤPUnitZeroIso :
    singularHomologyℤ 0 (TopCat.of PUnit) ≅ AddCommGrpCat.of ℤ :=
  singularHomologyPUnitZeroIso AddCommGrpCat.{0} (AddCommGrpCat.of ℤ)

/-- The augmentation `Hₙ(X; ℤ) → Hₙ(point; ℤ)` induced by the collapse map `X → point`. -/
noncomputable def singularHomologyℤAugmentation (n : ℕ) (X : TopCat.{0}) :
    singularHomologyℤ n X ⟶ singularHomologyℤ n (TopCat.of PUnit) :=
  (singularHomologyℤFunctor n).map (TopCat.isTerminalPUnit.from X)

/-- Reduced integral singular homology `H̃ₙ(X; ℤ)`, the kernel of the augmentation. -/
noncomputable def reducedSingularHomologyℤ (n : ℕ) (X : TopCat.{0}) : AddCommGrpCat.{0} :=
  kernel (singularHomologyℤAugmentation n X)

/-- The legacy integral augmentation is the integral component of the generic augmentation. -/
@[simp]
lemma singularHomologyℤAugmentation_eq_app (n : ℕ) (X : TopCat.{0}) :
    singularHomologyℤAugmentation n X =
      (singularHomologyAugmentation AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n).app X :=
  rfl

/-- The generic integral reduced homology object is canonically isomorphic to the legacy
objectwise kernel. -/
noncomputable def reducedSingularHomologyℤObjIso (n : ℕ) (X : TopCat.{0}) :
    reducedSingularHomology AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n X ≅
      reducedSingularHomologyℤ n X :=
  reducedSingularHomologyObjIso AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n X

@[reassoc]
lemma reducedSingularHomologyℤObjIso_hom_ι (n : ℕ) (X : TopCat.{0}) :
    (reducedSingularHomologyℤObjIso n X).hom ≫
        kernel.ι (singularHomologyℤAugmentation n X) =
      (reducedSingularHomologyι AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n).app X := by
  rw [reducedSingularHomologyℤObjIso]
  exact reducedSingularHomologyObjIso_hom_ι
    AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n X

/-- Reduced homology of a point vanishes in every degree. -/
theorem isZero_reducedSingularHomologyℤ_punit (n : ℕ) :
    IsZero (reducedSingularHomologyℤ n (TopCat.of PUnit)) :=
  (isZero_reducedSingularHomology_punit AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n).of_iso
    (reducedSingularHomologyℤObjIso n (TopCat.of PUnit)).symm

/-- In positive degrees the augmentation to a point vanishes, so reduced and unreduced
homology agree: `H̃ₙ(X; ℤ) ≅ Hₙ(X; ℤ)` for `n ≠ 0`. -/
noncomputable def reducedSingularHomologyℤIso (n : ℕ) (hn : n ≠ 0) (X : TopCat.{0}) :
    reducedSingularHomologyℤ n X ≅ singularHomologyℤ n X :=
  (reducedSingularHomologyℤObjIso n X).symm ≪≫
    (reducedSingularHomologyFunctorIso AddCommGrpCat.{0}
      (AddCommGrpCat.of ℤ) n hn).app X

/-- For a pointed space, homology splits as reduced homology plus the homology of a point:
`Hₙ(X; ℤ) ≅ H̃ₙ(X; ℤ) ⊕ Hₙ(point; ℤ)`. -/
noncomputable def singularHomologyℤIsoReducedBiprod (n : ℕ) {X : TopCat.{0}}
    (b : TopCat.of PUnit ⟶ X) :
    singularHomologyℤ n X ≅ reducedSingularHomologyℤ n X ⊞ singularHomologyℤ n (TopCat.of PUnit) :=
  singularHomologyIsoReducedBiprod AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n b ≪≫
    biprod.mapIso (reducedSingularHomologyℤObjIso n X) (Iso.refl _)

/-- Degree-zero splitting: `H₀(X; ℤ) ≅ H̃₀(X; ℤ) ⊕ ℤ` for a pointed space. -/
noncomputable def singularHomologyℤZeroIsoReducedBiprod {X : TopCat.{0}}
    (b : TopCat.of PUnit ⟶ X) :
    singularHomologyℤ 0 X ≅ reducedSingularHomologyℤ 0 X ⊞ AddCommGrpCat.of ℤ :=
  singularHomologyℤIsoReducedBiprod 0 b ≪≫ biprod.mapIso (Iso.refl _) singularHomologyℤPUnitZeroIso

/-- Homotopy invariance: homotopic maps induce equal maps on integral homology. -/
theorem singularHomologyℤ_map_eq_of_homotopy (n : ℕ) {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) :
    (singularHomologyℤFunctor n).map f = (singularHomologyℤFunctor n).map g :=
  singularHomology_map_eq_of_homotopy AddCommGrpCat.{0} H (AddCommGrpCat.of ℤ) n

/-- A homotopy equivalence `f : X ⟶ Y` with homotopy inverse `g` induces an isomorphism
`Hₙ(X; ℤ) ≅ Hₙ(Y; ℤ)`. -/
noncomputable def singularHomologyℤMapIso (n : ℕ) {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X)) (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    singularHomologyℤ n X ≅ singularHomologyℤ n Y :=
  singularHomologyMapIso AddCommGrpCat.{0} n f g hfg hgf (AddCommGrpCat.of ℤ)

@[simp] theorem singularHomologyℤMapIso_hom (n : ℕ) {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X)) (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    (singularHomologyℤMapIso n f g hfg hgf).hom = (singularHomologyℤFunctor n).map f := rfl

@[simp] theorem singularHomologyℤMapIso_inv (n : ℕ) {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X)) (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    (singularHomologyℤMapIso n f g hfg hgf).inv = (singularHomologyℤFunctor n).map g := rfl

/-- For a contractible space, the degree-0 augmentation to a point is an isomorphism. -/
instance isIso_augmentation_zero_of_contractible (Y : Type) [TopologicalSpace Y]
    [ContractibleSpace Y] : IsIso (singularHomologyℤAugmentation 0 (TopCat.of Y)) := by
  have : PathConnectedSpace (TopCat.of Y) := inferInstance
  rw [singularHomologyℤAugmentation_eq_app]
  exact isIso_singularHomologyAugmentationAppZero_of_pathConnectedSpace
    AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) (TopCat.of Y)

/-- A contractible space has trivial homology in positive degrees. -/
theorem isZero_singularHomologyℤ_of_contractible (n : ℕ) (hn : n ≠ 0) (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] : IsZero (singularHomologyℤ n (TopCat.of X)) :=
  isZero_singularHomology_of_contractible AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n hn X

/-- A contractible space has `H₀(X; ℤ) ≅ ℤ`. -/
noncomputable def singularHomologyℤContractibleZeroIso (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] : singularHomologyℤ 0 (TopCat.of X) ≅ AddCommGrpCat.of ℤ :=
  singularHomologyZeroIso_of_contractible AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) X

theorem isZero_reducedSingularHomologyℤ_of_contractible (n : ℕ) (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (reducedSingularHomologyℤ n (TopCat.of X)) := by
  have hGen : IsZero
      (reducedSingularHomology AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n (TopCat.of X)) :=
    isZero_reducedSingularHomology_of_contractible AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) n X
  exact hGen.of_iso (reducedSingularHomologyℤObjIso n (TopCat.of X)).symm

/-- The integral singular chain-complex functor `TopCat ⥤ ChainComplex Ab ℕ`. -/
noncomputable abbrev singularChainℤFunctor : TopCat.{0} ⥤ ChainComplex AddCommGrpCat.{0} ℕ :=
  (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)

/-- The singular chain map `C(A) ⟶ C(X)` induced by `i : A ⟶ X`. -/
noncomputable abbrev singularChainℤMap {A X : TopCat.{0}} (i : A ⟶ X) :
    singularChainℤFunctor.obj A ⟶ singularChainℤFunctor.obj X :=
  singularChainℤFunctor.map i

end AlgebraicTopology
