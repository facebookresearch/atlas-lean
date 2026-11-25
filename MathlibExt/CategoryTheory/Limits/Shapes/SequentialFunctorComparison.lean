/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOne
public import MathlibExt.CategoryTheory.Limits.Shapes.ProductFunctorComparison
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Functor comparison for sequential differences

The native product comparison intertwines the standard sequential differences
for every additive functor. Its naturality also compares maps of towers.
Product preservation makes this comparison an isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [HasCountableProducts C] [HasCountableProducts D]

/-- The native product comparison is natural in maps of inverse towers. -/
@[reassoc]
theorem sequentialProductMap_piComparison
    (F : C ⥤ D) {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    F.map (sequentialProductMap α) ≫
        piComparison F (fun n : ℕ => B.obj (op n)) =
      piComparison F (fun n : ℕ => A.obj (op n)) ≫
        sequentialProductMap (Functor.whiskerRight α F) := by
  change F.map (Pi.map (fun n : ℕ => α.app (op n))) ≫
      piComparison F (fun n : ℕ => B.obj (op n)) =
    piComparison F (fun n : ℕ => A.obj (op n)) ≫
      Pi.map (fun n : ℕ => F.map (α.app (op n)))
  exact Pi.map_piComparison F
    (f := fun n : ℕ => A.obj (op n))
    (g := fun n : ℕ => B.obj (op n)) (fun n : ℕ => α.app (op n))

variable [Preadditive C] [Preadditive D]

/-- The standard difference is identity minus the native product map
reindexed by successor. -/
theorem sequentialDifference_eq_id_sub_map' (A : ℕᵒᵖ ⥤ C) :
    sequentialDifference A = 𝟙 (sequentialProduct A) -
      Pi.map' Nat.succ (fun n => A.map (homOfLE (Nat.le_succ n)).op) := by
  apply Pi.hom_ext
  intro n
  simp only [sequentialDifference_π, Preadditive.sub_comp,
    Category.id_comp, Pi.map'_comp_π]

/-- Mapping the standard difference commutes with the native product
comparison for an additive functor. -/
@[reassoc]
theorem sequentialDifference_piComparison
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C) :
    F.map (sequentialDifference A) ≫
        piComparison F (fun n : ℕ => A.obj (op n)) =
      piComparison F (fun n : ℕ => A.obj (op n)) ≫
        sequentialDifference (A ⋙ F) := by
  rw [sequentialDifference_eq_id_sub_map' A,
    sequentialDifference_eq_id_sub_map' (A ⋙ F)]
  simp only [Functor.map_sub, Functor.map_id, Preadditive.sub_comp,
    Preadditive.comp_sub, Category.id_comp]
  change _ =
    (piComparison F (fun n : ℕ => A.obj (op n))) ≫
      𝟙 (∏ᶜ fun n : ℕ => F.obj (A.obj (op n))) -
      (piComparison F (fun n : ℕ => A.obj (op n))) ≫
        Pi.map' Nat.succ (fun n => F.map (A.map (homOfLE (Nat.le_succ n)).op))
  rw [Category.comp_id]
  exact
    congrArg (fun h => piComparison F (fun n : ℕ => A.obj (op n)) - h)
      (Pi.map'_piComparison F Nat.succ
        (f := fun n : ℕ => A.obj (op n))
        (g := fun n : ℕ => A.obj (op n))
        (fun n => A.map (homOfLE (Nat.le_succ n)).op))

/-- Preservation of the particular sequential product transports
epimorphisms between the mapped difference and the difference of the mapped tower. -/
theorem epi_map_sequentialDifference_iff
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    Epi (F.map (sequentialDifference A)) ↔ Epi (sequentialDifference (A ⋙ F)) := by
  rw [← epi_comp_iff_of_isIso (F.map (sequentialDifference A))
    (piComparison F (fun n : ℕ => A.obj (op n))),
    sequentialDifference_piComparison F A, epi_comp_iff_of_epi]

/-- Preservation of the particular sequential product transports
monomorphisms between the mapped difference and the difference of the mapped tower. -/
theorem mono_map_sequentialDifference_iff
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    Mono (F.map (sequentialDifference A)) ↔ Mono (sequentialDifference (A ⋙ F)) := by
  rw [← mono_comp_iff_of_mono (F.map (sequentialDifference A))
    (piComparison F (fun n : ℕ => A.obj (op n))),
    sequentialDifference_piComparison F A, mono_comp_iff_of_isIso]

/-- A functor reflecting epimorphisms detects an epimorphic standard
difference after mapping the tower and preserving its product. -/
theorem epi_sequentialDifference_of_epi_functor
    (F : C ⥤ D) [F.Additive] [Functor.ReflectsEpimorphisms F]
    (A : ℕᵒᵖ ⥤ C)
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F]
    [Epi (sequentialDifference (A ⋙ F))] : Epi (sequentialDifference A) :=
  Functor.epi_of_epi_map F ((epi_map_sequentialDifference_iff F A).2 inferInstance)

section Kernels

/-- Product preservation compares the kernel of the mapped difference with
that of the mapped tower. No kernel preservation by the functor is needed. -/
noncomputable def sequentialDifferenceKernelIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    kernel (F.map (sequentialDifference A)) ≅
      kernel (sequentialDifference (A ⋙ F)) :=
  kernel.mapIso (F.map (sequentialDifference A))
    (sequentialDifference (A ⋙ F))
    (PreservesProduct.iso F (fun n : ℕ => A.obj (op n)))
    (PreservesProduct.iso F (fun n : ℕ => A.obj (op n)))
    (by simpa only [PreservesProduct.iso_hom] using sequentialDifference_piComparison F A)

/-- The mapped-difference kernel isomorphism preserves the actual inclusions. -/
@[reassoc (attr := simp)]
theorem sequentialDifferenceKernelIso_hom_comp_ι
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    (sequentialDifferenceKernelIso F A).hom ≫
        kernel.ι (sequentialDifference (A ⋙ F)) =
      kernel.ι (F.map (sequentialDifference A)) ≫
        piComparison F (fun n : ℕ => A.obj (op n)) := by
  dsimp only [sequentialDifferenceKernelIso, kernel.mapIso]
  simp only [kernel.map, kernel.lift_ι, PreservesProduct.iso_hom]

/-- The inverse kernel isomorphism preserves the actual inclusions. -/
@[reassoc (attr := simp)]
theorem sequentialDifferenceKernelIso_inv_comp_ι
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    (sequentialDifferenceKernelIso F A).inv ≫
        kernel.ι (F.map (sequentialDifference A)) =
      kernel.ι (sequentialDifference (A ⋙ F)) ≫
        (PreservesProduct.iso F (fun n : ℕ => A.obj (op n))).inv := by
  dsimp only [sequentialDifferenceKernelIso, kernel.mapIso]
  simp only [kernel.map, kernel.lift_ι]

/-- The kernel comparison for a sequential difference, followed by the
kernel map induced by the native product comparison. -/
noncomputable def sequentialKernelComparison
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (sequentialDifference A)]
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))] :
    F.obj (kernel (sequentialDifference A)) ⟶ kernel (sequentialDifference (A ⋙ F)) :=
  kernelComparison (sequentialDifference A) F ≫
    kernel.map (F.map (sequentialDifference A)) (sequentialDifference (A ⋙ F))
      (piComparison F (fun n : ℕ => A.obj (op n)))
      (piComparison F (fun n : ℕ => A.obj (op n)))
      (sequentialDifference_piComparison F A)

/-- The kernel comparison preserves the actual kernel inclusions. -/
@[reassoc (attr := simp)]
theorem sequentialKernelComparison_comp_ι
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (sequentialDifference A)]
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))] :
    sequentialKernelComparison F A ≫ kernel.ι (sequentialDifference (A ⋙ F)) =
      F.map (kernel.ι (sequentialDifference A)) ≫
        piComparison F (fun n : ℕ => A.obj (op n)) := by
  dsimp only [sequentialKernelComparison]
  simp only [Category.assoc, kernel.map, kernel.lift_ι,
    kernelComparison_comp_ι_assoc]

/-- Preserving the product and the particular kernel makes the kernel
comparison an isomorphism. -/
noncomputable instance sequentialKernelComparison_isIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (sequentialDifference A)]
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F]
    [PreservesLimit (parallelPair (sequentialDifference A) 0) F] :
    IsIso (sequentialKernelComparison F A) := by
  dsimp only [sequentialKernelComparison]
  infer_instance

/-- The kernel isomorphism has the actual kernel comparison as its hom. -/
noncomputable def sequentialKernelFunctorIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (sequentialDifference A)]
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F]
    [PreservesLimit (parallelPair (sequentialDifference A) 0) F] :
    F.obj (kernel (sequentialDifference A)) ≅ kernel (sequentialDifference (A ⋙ F)) :=
  asIso (sequentialKernelComparison F A)

@[simp]
theorem sequentialKernelFunctorIso_hom
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (sequentialDifference A)]
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F]
    [PreservesLimit (parallelPair (sequentialDifference A) 0) F] :
    (sequentialKernelFunctorIso F A).hom = sequentialKernelComparison F A := rfl

end Kernels

section Cokernels

/-- Product preservation compares cokernels of the two standard differences.
This concerns the cokernel of the mapped difference and needs no preservation
of cokernels by the functor. -/
noncomputable def sequentialDifferenceCokernelIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasCokernel (F.map (sequentialDifference A))]
    [HasCokernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    cokernel (F.map (sequentialDifference A)) ≅
      cokernel (sequentialDifference (A ⋙ F)) :=
  cokernel.mapIso (F.map (sequentialDifference A))
    (sequentialDifference (A ⋙ F))
    (PreservesProduct.iso F (fun n : ℕ => A.obj (op n)))
    (PreservesProduct.iso F (fun n : ℕ => A.obj (op n)))
    (by simpa only [PreservesProduct.iso_hom] using sequentialDifference_piComparison F A)

/-- The mapped-difference cokernel isomorphism preserves the quotient maps. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_sequentialDifferenceCokernelIso_hom
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasCokernel (F.map (sequentialDifference A))]
    [HasCokernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    cokernel.π (F.map (sequentialDifference A)) ≫
        (sequentialDifferenceCokernelIso F A).hom =
      piComparison F (fun n : ℕ => A.obj (op n)) ≫
        cokernel.π (sequentialDifference (A ⋙ F)) := by
  dsimp only [sequentialDifferenceCokernelIso, cokernel.mapIso]
  simp only [cokernel.map, cokernel.π_desc, PreservesProduct.iso_hom]

/-- The inverse cokernel isomorphism preserves the quotient maps. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_sequentialDifferenceCokernelIso_inv
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasCokernel (F.map (sequentialDifference A))]
    [HasCokernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    cokernel.π (sequentialDifference (A ⋙ F)) ≫
        (sequentialDifferenceCokernelIso F A).inv =
      (PreservesProduct.iso F (fun n : ℕ => A.obj (op n))).inv ≫
        cokernel.π (F.map (sequentialDifference A)) := by
  dsimp only [sequentialDifferenceCokernelIso, cokernel.mapIso]
  simp only [cokernel.map, cokernel.π_desc]

variable [HasCokernels C] [HasCokernels D]

/-- Preservation of the particular cokernel gives a map from the image of
concrete sequential lim-one to the lim-one of the mapped tower. -/
noncomputable def sequentialLimOneComparison
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F] :
    F.obj (sequentialLimOne A) ⟶ sequentialLimOne (A ⋙ F) :=
  (PreservesCokernel.iso F (sequentialDifference A)).hom ≫
    cokernel.map (F.map (sequentialDifference A)) (sequentialDifference (A ⋙ F))
      (piComparison F (fun n : ℕ => A.obj (op n)))
      (piComparison F (fun n : ℕ => A.obj (op n)))
      (sequentialDifference_piComparison F A)

/-- The lim-one comparison preserves the actual quotient maps. -/
@[reassoc (attr := simp)]
theorem map_sequentialLimOneπ_comp_comparison
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F] :
    F.map (sequentialLimOneπ A) ≫ sequentialLimOneComparison F A =
      piComparison F (fun n : ℕ => A.obj (op n)) ≫ sequentialLimOneπ (A ⋙ F) := by
  change F.map (cokernel.π (sequentialDifference A)) ≫
    ((PreservesCokernel.iso F (sequentialDifference A)).hom ≫
      cokernel.map (F.map (sequentialDifference A)) (sequentialDifference (A ⋙ F))
        (piComparison F (fun n : ℕ => A.obj (op n)))
        (piComparison F (fun n : ℕ => A.obj (op n)))
        (sequentialDifference_piComparison F A)) =
      piComparison F (fun n : ℕ => A.obj (op n)) ≫
        cokernel.π (sequentialDifference (A ⋙ F))
  simp only [PreservesCokernel.π_iso_hom_assoc, cokernel.π_desc]

/-- Product preservation makes the concrete lim-one comparison invertible. -/
noncomputable instance sequentialLimOneComparison_isIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    IsIso (sequentialLimOneComparison F A) := by
  change IsIso
    (((PreservesCokernel.iso F (sequentialDifference A)).hom :
        F.obj (cokernel (sequentialDifference A)) ⟶
          cokernel (F.map (sequentialDifference A))) ≫
      (cokernel.map (F.map (sequentialDifference A)) (sequentialDifference (A ⋙ F))
        (piComparison F (fun n : ℕ => A.obj (op n)))
        (piComparison F (fun n : ℕ => A.obj (op n)))
        (sequentialDifference_piComparison F A) :
          cokernel (F.map (sequentialDifference A)) ⟶
            cokernel (sequentialDifference (A ⋙ F))))
  infer_instance

/-- The image of concrete lim-one agrees with the lim-one of the mapped
tower when the particular product and cokernel are preserved. -/
noncomputable def sequentialLimOneFunctorIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    F.obj (sequentialLimOne A) ≅ sequentialLimOne (A ⋙ F) :=
  asIso (sequentialLimOneComparison F A)

@[simp]
theorem sequentialLimOneFunctorIso_hom
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    (sequentialLimOneFunctorIso F A).hom = sequentialLimOneComparison F A := rfl

end Cokernels

end CategoryTheory.Limits
