/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.CokernelCompShortExact

/-! # Tests for the cokernel-composite short exact sequence -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace CategoryTheory.CokernelCompShortExactTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

example : ShortComplex C := cokernelCompShortComplex f g

example : (cokernelCompShortComplex f g).Exact :=
  cokernelCompShortComplex_exact f g

example [Mono g] : (cokernelCompShortComplex f g).ShortExact :=
  cokernelCompShortComplex_shortExact f g

example {X' : C} (e : X' ≅ X) :
    cokernelCompShortComplex (e.hom ≫ f) g ≅
      cokernelCompShortComplex f g :=
  cokernelCompShortComplexPrecompIso f g e

example {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) :
    cokernelCompShortComplex f' g ≅ cokernelCompShortComplex f g :=
  cokernelCompShortComplexPrecompIsoOfEq f g e f' h

example {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) :
    (cokernelCompShortComplexPrecompIsoOfEq f g e f' h).hom.τ₃ = 𝟙 _ :=
  cokernelCompShortComplexPrecompIsoOfEq_hom_τ₃ f g e f' h

example {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) {T : ShortComplex C}
    (E : cokernelCompShortComplex f g ≅ T) :
    ((cokernelCompShortComplexPrecompIsoOfEq f g e f' h ≪≫ E).hom.τ₃) =
      E.hom.τ₃ :=
  cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₃ f g e f' h E

end CategoryTheory.CokernelCompShortExactTests

end
