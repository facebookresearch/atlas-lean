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
# Additive functors and sequential difference comparisons

Let C,D be preadditive categories with countable products and F : C ⥤ D additive, with
independent object and morphism universes. For an inverse tower A with transition t_n :
A_{n+1} → A_n, put P_A = ∏ₙA_n and d_A = 1−shift, where d_A ≫ π_n = π_n−π_{n+1} ≫ t_n. The
product comparison κ_A : F(P_A) → P_{A⋙F} satisfies F(d_A) ≫ κ_A = κ_A ≫ d_{A⋙F}, naturally in
tower maps.

Preservation of the particular product P_A makes κ_A invertible. It then identifies the
kernels and cokernels of F(d_A) and d_{A⋙F}. To identify F(Ker(d_A)) with Ker(d_{A⋙F})
requires preservation of the particular kernel as well. Likewise, preservation of the
particular cokernel gives the comparison F(Coker(d_A)) → Coker(d_{A⋙F}), which is invertible
when the product is also preserved. The sequential lim¹ object here is Coker(d_A).
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

/-- Product comparison naturality for inverse tower maps.

Let F : C ⥤ D be any functor between categories with countable products and α : A → B a map of
inverse towers. Writing P(α) for its componentwise product map, the canonical comparisons
satisfy F(P(α)) ≫ κ_B = κ_A ≫ P(α⋙F). This equation does not require additivity. -/
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

/-- Sequential difference as identity minus successor shift.

For an inverse tower A in a preadditive category with countable products, let t_n : A_{n+1} →
A_n be its transitions. The standard difference on P_A = ∏ₙA_n is id_{P_A} −
Pi.map'(Nat.succ,t), so its n-th projection is π_n − π_{n+1} ≫ t_n. -/
theorem sequentialDifference_eq_id_sub_map' (A : ℕᵒᵖ ⥤ C) :
    sequentialDifference A = 𝟙 (sequentialProduct A) -
      Pi.map' Nat.succ (fun n => A.map (homOfLE (Nat.le_succ n)).op) := by
  apply Pi.hom_ext
  intro n
  simp only [sequentialDifference_π, Preadditive.sub_comp,
    Category.id_comp, Pi.map'_comp_π]

/-- Intertwining sequential differences by an additive product comparison.

For an additive functor F between preadditive categories with countable products and an
inverse tower A, the product comparison κ_A satisfies F(d_A) ≫ κ_A = κ_A ≫ d_{A⋙F}. Here d_A
is identity minus successor shift; additivity preserves the subtraction and the mapped
transition maps. -/
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

/-- Epimorphism comparison for a mapped sequential difference.

Let F be additive between preadditive categories with countable products and preserve the
particular product P_A of an inverse tower A. The resulting invertible comparison κ_A
intertwines F(d_A) and d_{A⋙F}, hence F(d_A) is epic if and only if d_{A⋙F} is epic. -/
theorem epi_map_sequentialDifference_iff
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    Epi (F.map (sequentialDifference A)) ↔ Epi (sequentialDifference (A ⋙ F)) := by
  rw [← epi_comp_iff_of_isIso (F.map (sequentialDifference A))
    (piComparison F (fun n : ℕ => A.obj (op n))),
    sequentialDifference_piComparison F A, epi_comp_iff_of_epi]

/-- Monomorphism comparison for a mapped sequential difference.

Let F be additive between preadditive categories with countable products and preserve the
particular product P_A of an inverse tower A. Since κ_A is invertible and F(d_A) ≫ κ_A = κ_A ≫
d_{A⋙F}, the morphism F(d_A) is monic if and only if d_{A⋙F} is monic. -/
theorem mono_map_sequentialDifference_iff
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    Mono (F.map (sequentialDifference A)) ↔ Mono (sequentialDifference (A ⋙ F)) := by
  rw [← mono_comp_iff_of_mono (F.map (sequentialDifference A))
    (piComparison F (fun n : ℕ => A.obj (op n))),
    sequentialDifference_piComparison F A, mono_comp_iff_of_isIso]

/-- Detecting an epic tower difference through an additive functor.

Suppose F : C ⥤ D is additive, reflects epimorphisms and preserves the product of an inverse
tower A, with C,D preadditive and having countable products. If d_{A⋙F} is epic, the product
comparison makes F(d_A) epic, and reflection implies that d_A is epic. -/
theorem epi_sequentialDifference_of_epi_functor
    (F : C ⥤ D) [F.Additive] [Functor.ReflectsEpimorphisms F]
    (A : ℕᵒᵖ ⥤ C)
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F]
    [Epi (sequentialDifference (A ⋙ F))] : Epi (sequentialDifference A) :=
  Functor.epi_of_epi_map F ((epi_map_sequentialDifference_iff F A).2 inferInstance)

section Kernels

/-- Kernel isomorphism induced by preservation of a tower product.

Let F be additive between preadditive categories with countable products and preserve P_A. If
the kernels of F(d_A) and d_{A⋙F} exist, the square with invertible sides κ_A induces an
isomorphism Ker(F(d_A)) ≅ Ker(d_{A⋙F}). Preservation of Ker(d_A) by F is not an assumption of
this comparison. -/
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

/-- Forward mapped-difference kernel comparison on inclusions.

With additive F preserving P_A and both mapped-difference kernels defined, let e : Ker(F(d_A))
≅ Ker(d_{A⋙F}) be the induced kernel comparison. Its forward map satisfies e.hom ≫
kernel.ι(d_{A⋙F}) = kernel.ι(F(d_A)) ≫ κ_A. -/
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

/-- Inverse mapped-difference kernel comparison on inclusions.

With additive F preserving P_A and both kernels defined, the induced isomorphism e :
Ker(F(d_A)) ≅ Ker(d_{A⋙F}) satisfies e.inv ≫ kernel.ι(F(d_A)) = kernel.ι(d_{A⋙F}) ≫ κ_A⁻¹.
Here κ_A is the invertible product comparison. -/
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

/-- Comparison from the image of a tower kernel to the mapped tower kernel.

For additive F between preadditive categories with countable products, suppose Ker(d_A),
Ker(F(d_A)) and Ker(d_{A⋙F}) exist. Compose the ordinary kernel comparison F(Ker(d_A)) →
Ker(F(d_A)) with the kernel map induced by κ_A to obtain F(Ker(d_A)) → Ker(d_{A⋙F}). This map
is defined without a preservation hypothesis. -/
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

/-- Kernel inclusion equation for additive tower transport.

For additive F and an inverse tower A with all three comparison kernels defined, the map k_A :
F(Ker(d_A)) → Ker(d_{A⋙F}) satisfies k_A ≫ kernel.ι(d_{A⋙F}) = F(kernel.ι(d_A)) ≫ κ_A. The
equation specifies its composite with the mapped tower's kernel inclusion. -/
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

/-- Invertibility of the tower kernel comparison under preservation.

Let F be additive between preadditive categories with countable products. If it preserves the
product P_A and the particular kernel of d_A, with the comparison kernels defined, then the
map F(Ker(d_A)) → Ker(d_{A⋙F}) is invertible. -/
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

/-- Isomorphism between a transported tower kernel and the mapped tower kernel.

For additive F preserving the product P_A and the kernel of d_A, the canonical kernel
comparison defines F(Ker(d_A)) ≅ Ker(d_{A⋙F}). The categories are preadditive with countable
products, and the three kernels occurring in the comparison are assumed to exist. -/
noncomputable def sequentialKernelFunctorIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [HasKernel (sequentialDifference A)]
    [HasKernel (F.map (sequentialDifference A))]
    [HasKernel (sequentialDifference (A ⋙ F))]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F]
    [PreservesLimit (parallelPair (sequentialDifference A) 0) F] :
    F.obj (kernel (sequentialDifference A)) ≅ kernel (sequentialDifference (A ⋙ F)) :=
  asIso (sequentialKernelComparison F A)

/-- Forward map of the transported tower kernel isomorphism.

Under preservation of P_A and Ker(d_A) by an additive functor F, the hom of
sequentialKernelFunctorIso is exactly sequentialKernelComparison F A : F(Ker(d_A)) →
Ker(d_{A⋙F}), with the comparison kernels defined. -/
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

/-- Cokernel isomorphism induced by preservation of a tower product.

Let F be additive between preadditive categories with countable products and preserve P_A. If
the cokernels of F(d_A) and d_{A⋙F} exist, the invertible product comparison κ_A induces
Coker(F(d_A)) ≅ Coker(d_{A⋙F}). This comparison uses the cokernel of the mapped difference and
does not require F to preserve Coker(d_A). -/
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

/-- Forward mapped-difference cokernel comparison on projections.

For additive F preserving P_A and both cokernels defined, let e : Coker(F(d_A)) ≅
Coker(d_{A⋙F}) be induced by κ_A. Its hom satisfies cokernel.π(F(d_A)) ≫ e.hom = κ_A ≫
cokernel.π(d_{A⋙F}). -/
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

/-- Inverse mapped-difference cokernel comparison on projections.

For additive F preserving P_A and both cokernels defined, the induced comparison e satisfies
cokernel.π(d_{A⋙F}) ≫ e.inv = κ_A⁻¹ ≫ cokernel.π(F(d_A)). Thus its inverse respects the
quotient projections through the inverse product comparison. -/
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

/-- Comparison for the cokernel of an additive tower difference.

Let C,D be preadditive with countable products and cokernels, and F additive. If F preserves
the particular cokernel of d_A, compose F(Coker(d_A)) ≅ Coker(F(d_A)) with the cokernel map
induced by κ_A. This defines F(lim¹ A) → lim¹(A⋙F), where lim¹ is the concrete cokernel of the
sequential difference. -/
noncomputable def sequentialLimOneComparison
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F] :
    F.obj (sequentialLimOne A) ⟶ sequentialLimOne (A ⋙ F) :=
  (PreservesCokernel.iso F (sequentialDifference A)).hom ≫
    cokernel.map (F.map (sequentialDifference A)) (sequentialDifference (A ⋙ F))
      (piComparison F (fun n : ℕ => A.obj (op n)))
      (piComparison F (fun n : ℕ => A.obj (op n)))
      (sequentialDifference_piComparison F A)

/-- Quotient projection equation for the sequential lim-one comparison.

For additive F preserving the cokernel of d_A, with countable products and cokernels in C,D,
let c_A : F(lim¹ A) → lim¹(A⋙F) be the canonical comparison. If q_A : P_A → lim¹ A is the
cokernel projection, then F(q_A) ≫ c_A = κ_A ≫ q_{A⋙F}. -/
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

/-- Invertibility of the sequential lim-one comparison.

In preadditive categories with countable products and cokernels, an additive functor F
preserving both P_A and Coker(d_A) makes the canonical map F(lim¹ A) → lim¹(A⋙F) invertible.
The comparison combines the preserved cokernel isomorphism with the isomorphism induced by the
product comparison. -/
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

/-- Transported sequential lim-one isomorphism.

For an additive functor F between preadditive categories with countable products and
cokernels, preservation of the particular product P_A and cokernel of d_A gives F(lim¹ A) ≅
lim¹(A⋙F). Both lim¹ objects are defined as cokernels of their standard sequential
differences. -/
noncomputable def sequentialLimOneFunctorIso
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    F.obj (sequentialLimOne A) ≅ sequentialLimOne (A ⋙ F) :=
  asIso (sequentialLimOneComparison F A)

/-- Forward map of the sequential lim-one transport isomorphism.

When additive F preserves P_A and Coker(d_A), the hom of sequentialLimOneFunctorIso is
sequentialLimOneComparison F A : F(lim¹ A) → lim¹(A⋙F), the comparison characterized by its
equation with the cokernel projections. -/
@[simp]
theorem sequentialLimOneFunctorIso_hom
    (F : C ⥤ D) [F.Additive] (A : ℕᵒᵖ ⥤ C)
    [PreservesColimit (parallelPair (sequentialDifference A) 0) F]
    [PreservesLimit (Discrete.functor (fun n : ℕ => A.obj (op n))) F] :
    (sequentialLimOneFunctorIso F A).hom = sequentialLimOneComparison F A := rfl

end Cokernels

end CategoryTheory.Limits
