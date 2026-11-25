/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingIndex
public import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor

/-!
# Full-Hom naturality of the actual Day coefficient braid

The original external tensor actions commute with the value braid and the
actual swap of the entire product-enriched Hom object.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingCoefficients

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  (F G : EnrichedFunctor V I V)

/-- The original coefficient braid is natural over both complete enriched Hom factors. -/
theorem naturality (X Y : I × I) :
    MonoidalClosed.uncurry ((F.externalTensor G).map X Y) ≫
        (β_ (F.obj Y.1) (G.obj Y.2)).hom =
      ((β_ (F.obj X.1) (G.obj X.2)).hom ⊗ₘ (BraidingIndex.swap (V := V)).map X Y) ≫
        MonoidalClosed.uncurry ((G.externalTensor F).map (X.2, X.1) (Y.2, Y.1)) := by
  let A : V := F.obj X.1
  let B : V := G.obj X.2
  let A' : V := F.obj Y.1
  let B' : V := G.obj Y.2
  let H : V := X.1 ⟶[V] Y.1
  let K : V := X.2 ⟶[V] Y.2
  let f : A ⊗ H ⟶ A' := MonoidalClosed.uncurry (F.map X.1 Y.1)
  let g : B ⊗ K ⟶ B' := MonoidalClosed.uncurry (G.map X.2 Y.2)
  have hl : MonoidalClosed.uncurry ((F.externalTensor G).map X Y) =
      tensorμ A B H K ≫ (f ⊗ₘ g) := EnrichedFunctor.externalTensor_uncurry F G X Y
  have hr : MonoidalClosed.uncurry ((G.externalTensor F).map (X.2, X.1) (Y.2, Y.1)) =
      tensorμ B A K H ≫ (g ⊗ₘ f) :=
    EnrichedFunctor.externalTensor_uncurry G F (X.2, X.1) (Y.2, Y.1)
  have hn : (f ⊗ₘ g) ≫ (β_ A' B').hom =
      (β_ (A ⊗ H) (B ⊗ K)).hom ≫ (g ⊗ₘ f) := braiding_naturality f g
  have hm : tensorμ A B H K ≫ (β_ (A ⊗ H) (B ⊗ K)).hom =
      ((β_ A B).hom ⊗ₘ (β_ H K).hom) ≫ tensorμ B A K H :=
    BraidingCoherence.tensorMu_swap A B H K
  change MonoidalClosed.uncurry ((F.externalTensor G).map X Y) ≫ (β_ A' B').hom =
    ((β_ A B).hom ⊗ₘ (β_ H K).hom) ≫
      MonoidalClosed.uncurry ((G.externalTensor F).map (X.2, X.1) (Y.2, Y.1))
  calc
    _ = tensorμ A B H K ≫ (f ⊗ₘ g) ≫ (β_ A' B').hom := by
      exact (congrArg (fun t => t ≫ (β_ A' B').hom) hl).trans
        (Category.assoc (tensorμ A B H K) (f ⊗ₘ g) (β_ A' B').hom)
    _ = tensorμ A B H K ≫ (β_ (A ⊗ H) (B ⊗ K)).hom ≫ (g ⊗ₘ f) :=
      congrArg (fun t => tensorμ A B H K ≫ t) hn
    _ = ((β_ A B).hom ⊗ₘ (β_ H K).hom) ≫ tensorμ B A K H ≫ (g ⊗ₘ f) := by
      exact (Category.assoc (tensorμ A B H K)
        (β_ (A ⊗ H) (B ⊗ K)).hom (g ⊗ₘ f)).symm.trans
          ((congrArg (fun t => t ≫ (g ⊗ₘ f)) hm).trans
            (Category.assoc ((β_ A B).hom ⊗ₘ (β_ H K).hom)
              (tensorμ B A K H) (g ⊗ₘ f)))
    _ = _ := congrArg (fun t => ((β_ A B).hom ⊗ₘ (β_ H K).hom) ≫ t) hr.symm

end CategoryTheory.EnrichedDayKernel.BraidingCoefficients
