/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplexAugmentation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology of a mapped augmented complex in degrees zero and one

An additive functor preserving the augmentation cokernel identifies degree-zero homology of the
mapped complex with the image of the augmented object. If it preserves the next cokernel,
degree-one homology identifies with the kernel of the image of the augmentation-kernel inclusion.

The preservation assumptions concern individual cokernels; preservation of finite colimits
suffices. These are structural homology identifications for the complex and its augmentation maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ChainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {Q : ChainComplex C ℕ} {M : C}

/--
Degree-zero homology after applying a functor that preserves the augmentation cokernel. A
quasi-isomorphism in degree zero suffices.
-/
noncomputable def homologyZeroIsoOfPreservedAugmentation
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 0]
    [PreservesColimit (parallelPair (Q.d 1 0) 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology 0 ≅ F.obj M := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let c : CokernelCofork (Q.d 1 0) :=
    CokernelCofork.ofπ (π.f 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])
  have : Epi (π.f 0) := epi_augmentation_f_zero π
  let hc : IsColimit c := (exact_augmentation π).gIsCokernel
  exact K.isoHomologyι₀ ≪≫ K.opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    ((K.sc' 1 0 0).isoOpcyclesOfIsColimit
      (CokernelCofork.mapIsColimit c hc F)).symm

/--
The degree-zero identification carries the quotient projection to the image of the given
augmentation map.
-/
@[reassoc]
lemma pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 0]
    [PreservesColimit (parallelPair (Q.d 1 0) 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q)).inv ≫
      (homologyZeroIsoOfPreservedAugmentation F π).hom = F.map (π.f 0) := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let c : CokernelCofork (Q.d 1 0) :=
    CokernelCofork.ofπ (π.f 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])
  have : Epi (π.f 0) := epi_augmentation_f_zero π
  let hc : IsColimit c := (exact_augmentation π).gIsCokernel
  let e : (c.map F).pt ≅ (K.sc' 1 0 0).opcycles :=
    (K.sc' 1 0 0).isoOpcyclesOfIsColimit (CokernelCofork.mapIsColimit c hc F)
  change K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫
    (K.isoHomologyι₀.hom ≫ (K.opcyclesIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
      e.inv) = F.map (π.f 0)
  simp only [Iso.inv_hom_id_assoc,
    HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  exact (K.sc' 1 0 0).pOpcycles_π_isoOpcyclesOfIsColimit_inv
    (CokernelCofork.mapIsColimit c hc F)

variable {R : ChainComplex C ℕ} {N : C}

/-- The augmentation-kernel map induced by the degree-zero square. -/
noncomputable def augmentationKernelMap
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    kernel (π.f 0) ⟶ kernel (ρ.f 0) :=
  kernel.map (π.f 0) (ρ.f 0) (a.f 0) f h₀.symm

/-- The kernel map commutes with the two kernel inclusions. -/
@[reassoc]
lemma augmentationKernelMap_ι
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    augmentationKernelMap π ρ a f h₀ ≫ kernel.ι (ρ.f 0) =
      kernel.ι (π.f 0) ≫ a.f 0 :=
  kernel.lift_ι _ _ _

/-- The first differential lifts naturally to the augmentation kernels. -/
lemma kernelLift_augmentationKernelMap
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    kernel.lift (π.f 0) (Q.d 1 0)
        (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]) ≫
      augmentationKernelMap π ρ a f h₀ =
    a.f 1 ≫ kernel.lift (ρ.f 0) (R.d 1 0)
        (by rw [← ρ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]) := by
  apply (cancel_mono (kernel.ι (ρ.f 0))).1
  rw [Category.assoc, augmentationKernelMap_ι, kernel.lift_ι_assoc,
    Category.assoc, kernel.lift_ι]
  exact (a.comm 1 0).symm

/--
The preserved augmentation cokernel and its mapped kernel describe the degree-one right homology
of the original complex.
-/
noncomputable def augmentationRightHomologyData
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).sc' 2 1 0).RightHomologyData := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let q : Q.X 1 ⟶ kernel (π.f 0) :=
    kernel.lift (π.f 0) (Q.d 1 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])
  let k : kernel (π.f 0) ⟶ Q.X 0 := kernel.ι (π.f 0)
  have hqk : q ≫ k = Q.d 1 0 := kernel.lift_ι _ _ _
  let S : ShortComplex C := ShortComplex.mk (Q.d 2 1) q (by
    rw [← cancel_mono k, Category.assoc, hqk, Q.d_comp_d, zero_comp])
  have hS : S.Exact := exact_kernelLift_augmentation π
  have : Epi q := epi_kernelLift_augmentation π
  let c : CokernelCofork (Q.d 2 1) := CokernelCofork.ofπ q S.zero
  let hc : IsColimit c := hS.gIsCokernel
  let hp : IsColimit (c.map F) := CokernelCofork.mapIsColimit c hc F
  let T : ShortComplex D := K.sc' 2 1 0
  have hd : hp.desc (CokernelCofork.ofπ T.g T.zero) = F.map k := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc]
    change F.map (Q.d 1 0) = F.map q ≫ F.map k
    rw [← F.map_comp, hqk]
  exact
    { Q := F.obj (kernel (π.f 0))
      H := kernel (F.map k)
      p := F.map q
      ι := kernel.ι (F.map k)
      wp := (c.map F).condition
      hp := hp
      wι := by
        rw [hd]
        exact kernel.condition _
      hι := KernelFork.IsLimit.ofι' _ _ (fun g hg =>
        ⟨kernel.lift (F.map k) g (by simpa only [← hd] using hg),
          kernel.lift_ι _ _ _⟩) }

/-- The induced outgoing arrow of the chosen right homology data is the image
of the original augmentation-kernel inclusion. -/
lemma augmentationRightHomologyData_g'
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    (augmentationRightHomologyData F π).g' = F.map (kernel.ι (π.f 0)) := by
  apply (cancel_epi (augmentationRightHomologyData F π).p).1
  rw [ShortComplex.RightHomologyData.p_g']
  change F.map (Q.d 1 0) =
    F.map (kernel.lift (π.f 0) (Q.d 1 0) _) ≫ F.map (kernel.ι (π.f 0))
  rw [← F.map_comp, kernel.lift_ι]


/-- Degree-one homology is the kernel of the image of the augmentation-kernel
inclusion if the functor preserves the cokernel of the next differential. -/
noncomputable def homologyOneIsoOfPreservedKernelTail
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology 1 ≅
      kernel (F.map (kernel.ι (π.f 0))) :=
  ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homologyIsoSc'
    2 1 0 (by simp) (by simp) ≪≫ (augmentationRightHomologyData F π).homologyIso

/-- The degree-one comparison is constructed from the canonical augmentation homology data. -/
lemma homologyOneIsoOfPreservedKernelTail_eq
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    homologyOneIsoOfPreservedKernelTail F π =
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homologyIsoSc'
        2 1 0 (by simp) (by simp) ≪≫
          (augmentationRightHomologyData F π).homologyIso := rfl


end ChainComplex
