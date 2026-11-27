/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
Authors: @toskua, Codex
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Kernels of exact coproducts

Let C be an abelian category and I an indexing type. Assume that I-indexed
coproducts exist in C and that the colimit functor for the discrete category
on I preserves finite limits. For a family of morphisms fᵢ : Xᵢ → Yᵢ, there is
a canonical isomorphism
∐ᵢ ker(fᵢ) ≅ ker(∐ᵢ fᵢ).

On the i-th summand, its forward map is the kernel lift of
ker(fᵢ) → Xᵢ → ∐ᵢ Xᵢ. The inverse recovers the corresponding summand, and
the comparison commutes with maps induced by families of commuting squares.
The index, object and morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w} [HasColimitsOfShape (Discrete I) C]
  [HasExactColimitsOfShape (Discrete I) C]
variable {X Y : I → C} (f : ∀ i, X i ⟶ Y i)

/-- In an abelian category C with existing exact I-indexed coproducts, a family
fᵢ : Xᵢ → Yᵢ has the canonical comparison ∐ᵢ ker(fᵢ) ≅ ker(∐ᵢ fᵢ).
The index type and both category universes are independent. -/
def coproductKernelIso :
    (∐ fun i => kernel (f i)) ≅ kernel (Sigma.map f) := by
  let d : Discrete.functor X ⟶ Discrete.functor Y := Discrete.natTrans (fun i => f i.as)
  let G : (Discrete I ⥤ C) ⥤ C := colim
  let e : kernel d ≅ Discrete.functor (fun i => kernel (f i)) :=
    Discrete.natIso (fun i => PreservesKernel.iso ((evaluation (Discrete I) C).obj i) d)
  change G.obj (Discrete.functor (fun i => kernel (f i))) ≅ kernel (G.map d)
  exact G.mapIso e.symm ≪≫ PreservesKernel.iso G d

/-- For fᵢ : Xᵢ → Yᵢ in an abelian category with exact I-indexed coproducts,
the i-th summand of ∐ᵢ ker(fᵢ) ≅ ker(∐ᵢ fᵢ), followed by the kernel
inclusion, is ker(fᵢ) → Xᵢ → ∐ᵢ Xᵢ. -/
@[reassoc]
theorem coproductKernelIso_hom_ι (i : I) :
    Sigma.ι (fun i => kernel (f i)) i ≫ (coproductKernelIso f).hom ≫
        kernel.ι (Sigma.map f) =
      kernel.ι (f i) ≫ Sigma.ι X i := by
  let d : Discrete.functor X ⟶ Discrete.functor Y := Discrete.natTrans (fun i => f i.as)
  let G : (Discrete I ⥤ C) ⥤ C := colim
  let e : kernel d ≅ Discrete.functor (fun i => kernel (f i)) :=
    Discrete.natIso (fun i => PreservesKernel.iso ((evaluation (Discrete I) C).obj i) d)
  let χ : Discrete.functor (fun i => kernel (f i)) ⟶ Discrete.functor X := e.inv ≫ kernel.ι d
  change Sigma.ι (fun i => kernel (f i)) i ≫
      G.map e.inv ≫ (PreservesKernel.iso G d).hom ≫ kernel.ι (G.map d) = _
  rw [PreservesKernel.iso_hom]
  simp only [Category.assoc]
  rw [kernelComparison_comp_ι, ← G.map_comp]
  have hχ : χ.app (Discrete.mk i) = kernel.ι (f i) := by
    change (PreservesKernel.iso ((evaluation (Discrete I) C).obj (Discrete.mk i)) d).inv ≫
        ((evaluation (Discrete I) C).obj (Discrete.mk i)).map (kernel.ι d) = _
    exact PreservesKernel.iso_inv_ι ((evaluation (Discrete I) C).obj (Discrete.mk i)) d
  have hι :
      Sigma.ι (fun i => kernel (f i)) i ≫ G.map χ =
        χ.app (Discrete.mk i) ≫ Sigma.ι X i :=
    ι_colimMap χ (Discrete.mk i)
  exact hι.trans (congrArg (fun z => z ≫ Sigma.ι X i) hχ)

/-- For fᵢ : Xᵢ → Yᵢ in an abelian category with exact I-indexed coproducts,
the forward comparison on the i-th kernel summand is the unique lift of
ker(fᵢ) → Xᵢ → ∐ᵢ Xᵢ through ker(∐ᵢ fᵢ). -/
theorem ι_coproductKernelIso_hom (i : I) :
    Sigma.ι (fun i => kernel (f i)) i ≫ (coproductKernelIso f).hom =
      kernel.lift (Sigma.map f) (kernel.ι (f i) ≫ Sigma.ι X i) (by
        rw [Category.assoc, Sigma.ι_map, ← Category.assoc, kernel.condition, zero_comp]) := by
  apply (cancel_mono (kernel.ι (Sigma.map f))).1
  rw [Category.assoc, coproductKernelIso_hom_ι, kernel.lift_ι]

/-- For fᵢ : Xᵢ → Yᵢ in an abelian category with exact I-indexed coproducts,
the kernel lift of ker(fᵢ) → Xᵢ → ∐ᵢ Xᵢ, followed by the inverse
comparison, is the i-th injection into ∐ᵢ ker(fᵢ). -/
theorem kernel_lift_coproductKernelIso_inv (i : I) :
    kernel.lift (Sigma.map f) (kernel.ι (f i) ≫ Sigma.ι X i) (by
        rw [Category.assoc, Sigma.ι_map, ← Category.assoc, kernel.condition, zero_comp]) ≫
        (coproductKernelIso f).inv =
      Sigma.ι (fun i => kernel (f i)) i := by
  rw [← ι_coproductKernelIso_hom f i]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Let C be abelian with exact I-indexed coproducts. For families
fᵢ : Xᵢ → Yᵢ and gᵢ : X′ᵢ → Y′ᵢ, suppose uᵢ : Xᵢ → X′ᵢ and
vᵢ : Yᵢ → Y′ᵢ satisfy vᵢ ∘ fᵢ = gᵢ ∘ uᵢ. Taking the coproduct of
the induced kernel maps and then the comparison for g equals the
comparison for f followed by the kernel map of the coproduct square. -/
@[reassoc]
theorem coproductKernelIso_naturality
    {X' Y' : I → C} (g : ∀ i, X' i ⟶ Y' i)
    (u : ∀ i, X i ⟶ X' i) (v : ∀ i, Y i ⟶ Y' i)
    (h : ∀ i, f i ≫ v i = u i ≫ g i) :
    Sigma.map (fun i => kernel.map (f i) (g i) (u i) (v i) (h i)) ≫
        (coproductKernelIso g).hom =
      (coproductKernelIso f).hom ≫
        kernel.map (Sigma.map f) (Sigma.map g) (Sigma.map u) (Sigma.map v) (by
          apply Sigma.hom_ext
          intro i
          simpa only [Category.assoc, Sigma.ι_map, Sigma.ι_map_assoc] using
            congrArg (fun z : X i ⟶ Y' i => z ≫ Sigma.ι Y' i) (h i)) := by
  apply (cancel_mono (kernel.ι (Sigma.map g))).1
  apply Sigma.hom_ext
  intro i
  simp only [Category.assoc, Sigma.ι_map, Sigma.ι_map_assoc,
    coproductKernelIso_hom_ι, coproductKernelIso_hom_ι_assoc,
    kernel.map, kernel.lift_ι, kernel.lift_ι_assoc]

end CategoryTheory.Limits
