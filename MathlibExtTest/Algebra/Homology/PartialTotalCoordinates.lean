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

public import MathlibExt.Algebra.Homology.PartialTotalCoordinates

/-! Client tests for canonical partial-total coordinates. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {B B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

example (φ : B ⟶ B') (p : ℕ) (i : Fin (p + 1))
    (j n : ℕ) (hn : i.1 + j = n) :
    B.partialTotalComponent p i j n hn ≫ (B.partialTotalHom φ p).f n =
      (φ.f i.1).f j ≫ B'.partialTotalComponent p i j n hn :=
  B.partialTotalComponent_naturality φ p i j n hn

example (p : ℕ) (i : Fin (p + 1)) (j n : ℕ)
    (hn : i.1 + j = n) :
    B.partialTotalComponent p i j n hn ≫ (B.partialTotalι p).f n =
      B.ιTotal (ComplexShape.down ℕ) i.1 j n hn :=
  B.partialTotalComponent_comp_partialTotalι p i j n hn

#check HomologicalComplex₂.partialTotalComponent
#check HomologicalComplex₂.partialTotalComponent_naturality
#check HomologicalComplex₂.partialTotalComponent_comp_partialTotalι

example {p p' : ℕ} (h : p ≤ p') (i : Fin (p + 1))
    (j n : ℕ) (hn : i.1 + j = n) :
    B.partialTotalComponent p i j n hn ≫ (B.partialTotalMap h).f n =
      B.partialTotalComponent p' ⟨i.1, by omega⟩ j n hn :=
  B.partialTotalComponent_partialTotalMap h i j n hn

example (p : ℕ) {L : ChainComplex C ℕ}
    {f g : B.partialTotal p ⟶ L}
    (h : ∀ (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n),
      B.partialTotalComponent p i j n hn ≫ f.f n =
        B.partialTotalComponent p i j n hn ≫ g.f n) : f = g :=
  B.partialTotal_hom_ext p h

#check HomologicalComplex₂.partialTotalComponent_partialTotalMap
#check HomologicalComplex₂.partialTotal_hom_ext


#print axioms HomologicalComplex₂.partialTotalComponent_naturality
#print axioms HomologicalComplex₂.partialTotalComponent_comp_partialTotalι
#print axioms HomologicalComplex₂.partialTotal_hom_ext

end HomologicalComplex₂

end
