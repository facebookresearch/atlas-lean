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

public import MathlibExt.Algebra.Homology.PartialTotalEvenTail
public import Mathlib.CategoryTheory.Whiskering

/-!
# Natural total comparisons for initial-column quotients

The native partial-total cokernel already has a computed comparison with
its actual outer tail. This file exposes that comparison as a natural
isomorphism of the existing functors. For the first two columns, the even
outer offset gives the actual zero extension of the restricted total.
No periodicity isomorphism or comparison square is supplied by a caller.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace HomologicalComplex₂

section TailFunctors

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- Totalize the actual outer stupid tail at offset `s`. -/
def outerTailTotalFunctor (s : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ChainComplex C ℕ :=
  (partialTotalOuterEmbedding s).stupidTruncFunctor (ChainComplex C ℕ) ⋙
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- Restrict the outer complex, totalize it, then extend the total by the same offset. -/
def outerRestrictedTotalExtendFunctor (s : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ChainComplex C ℕ :=
  (partialTotalOuterEmbedding s).restrictionFunctor (ChainComplex C ℕ) ⋙
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⋙
      (partialTotalOuterEmbedding s).extendFunctor C

/-- The native outer-tail projection is natural before passing to its cokernel. -/
def partialTotalTailProjectionNatTrans (p : ℕ) :
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⟶
      outerTailTotalFunctor (C := C) (p + 1) where
  app K := total.map (natTailProjection K (p + 1)) (ComplexShape.down ℕ)
  naturality {K L} φ := by
    change total.map φ (ComplexShape.down ℕ) ≫
        total.map (natTailProjection L (p + 1)) (ComplexShape.down ℕ) =
      total.map (natTailProjection K (p + 1)) (ComplexShape.down ℕ) ≫
        total.map (stupidTruncMap φ (partialTotalOuterEmbedding (p + 1))) (ComplexShape.down ℕ)
    simpa only [total.map_comp] using
      congrArg (fun f => total.map f (ComplexShape.down ℕ))
        (natTailProjection_naturality φ (p + 1))

end TailFunctors

section CokernelComparisons

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual initial-column cokernel and native outer-tail total agree naturally. -/
def partialTotalCokernelTailNatIso (p : ℕ) :
    partialTotalCokernelFunctor (A := C) p ≅ outerTailTotalFunctor (C := C) (p + 1) :=
  NatIso.ofComponents (fun K => K.partialTotalCokernelTailIso p) (by
    intro K L φ
    exact partialTotalCokernelTailIso_hom_naturality φ p)

/-- The natural comparison preserves the original quotient projection. -/
theorem partialTotalCokernelπ_comp_tailNatIso (p : ℕ) :
    partialTotalCokernelπ (A := C) p ≫ (partialTotalCokernelTailNatIso (C := C) p).hom =
      partialTotalTailProjectionNatTrans (C := C) p := by
  apply NatTrans.ext
  funext K
  exact K.partialTotalCokernelTailIso_π p

/-- Quotienting by the first two columns gives the actual zero-extended restricted total,
functorially in the original bicomplex. The native offset is even. -/
def firstTwoColumnCokernelTailNatIso :
    partialTotalCokernelFunctor (A := C) 1 ≅ outerRestrictedTotalExtendFunctor (C := C) 2 :=
  NatIso.ofComponents (fun K => K.firstTwoColumnCokernelTailIso) (by
    intro K L φ
    exact firstTwoColumnCokernelTailIso_hom_naturality φ)

/-- The first-two-column natural comparison factors the quotient through the computed
outer-tail projection and the native even-extension/total comparison. -/
@[reassoc]
theorem firstTwoColumnCokernelTailNatIso_π
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    cokernel.π (K.partialTotalι 1) ≫ (firstTwoColumnCokernelTailNatIso (C := C)).hom.app K =
      total.map (natTailProjection K 2) (ComplexShape.down ℕ) ≫
        (evenOuterExtensionTotalIso
          (K.restriction (c := ComplexShape.down ℕ) (partialTotalOuterEmbedding 2)) 1).hom := by
  have paste {X Y Z W : ChainComplex C ℕ}
      (π : X ⟶ Y) (a : Y ⟶ Z) (b : Z ⟶ W) (q : X ⟶ Z)
      (h : π ≫ a = q) : π ≫ (a ≫ b) = q ≫ b :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ b) h)
  exact paste (cokernel.π (K.partialTotalι 1)) (K.partialTotalCokernelTailIso 1).hom
    (evenOuterExtensionTotalIso
      (K.restriction (c := ComplexShape.down ℕ) (partialTotalOuterEmbedding 2)) 1).hom
    (total.map (natTailProjection K 2) (ComplexShape.down ℕ))
    (K.partialTotalCokernelTailIso_π 1)

/-- Homology transports the same actual first-two-column comparison as a natural isomorphism.
The index remains the literal degree in the zero-extended target. -/
def firstTwoColumnCokernelTailHomologyNatIso (n : ℕ) :
    partialTotalCokernelFunctor (A := C) 1 ⋙ homologyFunctor C (ComplexShape.down ℕ) n ≅
      outerRestrictedTotalExtendFunctor (C := C) 2 ⋙ homologyFunctor C (ComplexShape.down ℕ) n :=
  Functor.isoWhiskerRight (firstTwoColumnCokernelTailNatIso (C := C))
    (homologyFunctor C (ComplexShape.down ℕ) n)

end CokernelComparisons

end HomologicalComplex₂
