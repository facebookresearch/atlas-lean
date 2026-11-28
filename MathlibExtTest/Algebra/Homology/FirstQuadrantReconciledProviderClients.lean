/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageDifferential

/-! # Consumers of the computed cokernel-comparison endpoints -/

@[expose] public section

open CategoryTheory

universe v u

namespace HomologicalComplex₂.FirstQuadrantReconciledProviderClients

variable {C : Type u} [Category.{v} C] [Abelian C]

example {X Y Z X' : CochainComplex C ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : X' ≅ X) (f' : X' ⟶ Y) (h : f' = e.hom ≫ f)
    {T : ShortComplex (CochainComplex C ℤ)}
    (E : CategoryTheory.cokernelCompShortComplex f g ≅ T) :
    (cokernelPrecompShortComplexIsoData f g e f' h E).1.hom.τ₃ = E.hom.τ₃ := by
  rfl

example {X Y Z X' : CochainComplex C ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : X' ≅ X) (f' : X' ⟶ Y) (h : f' = e.hom ≫ f)
    {T : ShortComplex (CochainComplex C ℤ)}
    (E : CategoryTheory.cokernelCompShortComplex f g ≅ T) :
    (cokernelPrecompShortComplexIsoData f g e f' h E).1 =
      CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq f g e f' h ≪≫ E :=
  (cokernelPrecompShortComplexIsoData f g e f' h E).2

end HomologicalComplex₂.FirstQuadrantReconciledProviderClients
