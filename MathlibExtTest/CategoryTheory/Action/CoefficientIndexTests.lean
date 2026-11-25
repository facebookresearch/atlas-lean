/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Action.CoefficientIndex

set_option autoImplicit false
noncomputable section

universe u v wH wE wF wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ActionCategory

section MinimalInputs

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) [Monoid H]
variable (E : Type wE) (F : Type wF) [MulAction H E] [MulAction H F]
variable (Z : C) (rho : H →* End Z)
variable [HasColimit (coefficientDiagram H E Z rho)]
variable [HasColimit (coefficientDiagram H F Z rho)]
variable (e : E ≃ F) (he : ∀ (a : H) x, e (a • x) = a • e x)

-- No group, tensor, coproduct, coequalizer or finite-index premise is available.
example : colimit (coefficientDiagram H E Z rho) ≅
    colimit (coefficientDiagram H F Z rho) :=
  coefficientColimitIndexIso H E F Z rho e he

example (i : E) :
    colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E) ≫
        (coefficientColimitIndexIso H E F Z rho e he).hom =
      colimit.ι (coefficientDiagram H F Z rho) (e i : ActionCategory H F) :=
  coefficientColimitIndexIso_generator H E F Z rho e he i

example (i : F) :
    colimit.ι (coefficientDiagram H F Z rho) (i : ActionCategory H F) ≫
        (coefficientColimitIndexIso H E F Z rho e he).inv =
      colimit.ι (coefficientDiagram H E Z rho) (e.symm i : ActionCategory H E) :=
  coefficientColimitIndexIso_inv_generator H E F Z rho e he i

example (Z' : C) (rho' : H →* End Z') (f : Z ⟶ Z')
    (hf : ∀ a, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
    [HasColimit (coefficientDiagram H E Z' rho')]
    [HasColimit (coefficientDiagram H F Z' rho')] :
    colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) ≫
        (coefficientColimitIndexIso H E F Z' rho' e he).hom =
      (coefficientColimitIndexIso H E F Z rho e he).hom ≫
        colimMap (coefficientNatTrans H F Z Z' rho rho' f hf) :=
  coefficientColimitIndexMap_naturality H E F Z rho Z' rho' f hf e he

example (t : E → E) (ht : ∀ (a : H) i, t (a • i) = a • t i)
    (s : F → F) (hs : ∀ (a : H) i, s (a • i) = a • s i)
    (hes : ∀ i, e (t i) = s (e i)) :
    coefficientColimitReindex H E Z rho t ht ≫
        (coefficientColimitIndexIso H E F Z rho e he).hom =
      (coefficientColimitIndexIso H E F Z rho e he).hom ≫
        coefficientColimitReindex H F Z rho s hs :=
  coefficientColimitIndexMap_reindex H E F Z rho e he t ht s hs hes

end MinimalInputs

section MinimalIdentity

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) [Monoid H]
variable (E : Type wE) [MulAction H E]
variable (Z : C) (rho : H →* End Z)
variable [HasColimit (coefficientDiagram H E Z rho)]

-- Only one index action and its one actual chosen coefficient colimit are available.
example : coefficientColimitIndexMap H E E Z rho id (fun _ _ => rfl) =
    𝟙 (colimit (coefficientDiagram H E Z rho)) :=
  coefficientColimitIndexMap_id H E Z rho

end MinimalIdentity

section MinimalComposition

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) [Monoid H]
variable (E : Type wE) (F : Type wF) (G : Type wG)
variable [MulAction H E] [MulAction H F] [MulAction H G]
variable (Z : C) (rho : H →* End Z)
variable [HasColimit (coefficientDiagram H E Z rho)]
variable [HasColimit (coefficientDiagram H F Z rho)]
variable [HasColimit (coefficientDiagram H G Z rho)]

-- The third index universe is independent and no group or coproduct premise is present.
example (t : E → F) (ht : ∀ (a : H) i, t (a • i) = a • t i)
    (s : F → G) (hs : ∀ (a : H) i, s (a • i) = a • s i) :
    coefficientColimitIndexMap H E F Z rho t ht ≫
        coefficientColimitIndexMap H F G Z rho s hs =
      coefficientColimitIndexMap H E G Z rho (s ∘ t)
        (fun a i => (congrArg s (ht a i)).trans (hs a (t i))) :=
  coefficientColimitIndexMap_comp H E F Z rho G t ht s hs

end MinimalComposition

#print axioms coefficientColimitIndexMap
#print axioms coefficientColimitIndexMap_generator
#print axioms coefficientIndexEquiv_symm_smul
#print axioms coefficientColimitIndexIso
#print axioms coefficientColimitIndexIso_generator
#print axioms coefficientColimitIndexIso_inv_generator
#print axioms coefficientColimitIndexMap_reindex
#print axioms coefficientColimitIndexMap_naturality
#print axioms coefficientColimitIndexMap_id
#print axioms coefficientColimitIndexMap_comp

end CategoryTheory.ActionCategory
