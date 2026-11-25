/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdColimit
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

@[expose] public section

/-!
# Concrete ProdColimit assembly regression (KQ3)

Fixed left `TopCat.of (Fin 2)` against the pushout span
`TopCat.of PUnit → TopCat.of (Fin 2)`, `TopCat.of PUnit → TopCat.of (Fin 3)`.
Preservation is obtained through `isColimitOfPreserves` with the fixed-left
all-colimits instance `TopCat.preservesColimits_prodFunctorObj`; the right-leg
pointwise check via `TopCat.prodMap_prodIso_inv_apply` and both projections
catches a swapped comparison direction, swapped span legs, or fixed-right use.
Asymmetry `Fin 2` vs `Fin 3` and the point `(1, 2)` keep the check non-vacuous.

API-reuse map: preservation reuses `TopCat.preservesColimits_prodFunctorObj`;
point transport reuses `TopCat.prodMap_prodIso_inv_apply`; leg projection
reuses `TopCat.prodIsoProd_inv_fst/snd`; the diagram composes Mathlib
`CategoryTheory.Limits.span`. No local reusable code is added.
No coproduct/coequalizer reproof, no realization or model-category claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

namespace MathlibExtTest.Topology.Category.TopCat.ProdColimitTests

/-- Asymmetric pushout-shaped span: `PUnit → Fin 2`, `PUnit → Fin 3`. -/
noncomputable def prodColimitSpan : WalkingSpan ⥤ TopCat.{0} :=
  CategoryTheory.Limits.span
    (TopCat.ofHom (ContinuousMap.const PUnit (0 : Fin 2)))
    (TopCat.ofHom (ContinuousMap.const PUnit (0 : Fin 3)))

/-- Fixed-left preservation plus right-leg pointwise check. -/
theorem prodColimit_pushout_fixedLeft_right_leg :
    Nonempty (IsColimit ((Limits.prod.functor.obj (TopCat.of (Fin 2))).mapCocone
      (colimit.cocone prodColimitSpan))) ∧
    (Limits.prod.fst : TopCat.of (Fin 2) ⨯ (colimit.cocone prodColimitSpan).pt ⟶
      TopCat.of (Fin 2))
      (((Limits.prod.functor.obj (TopCat.of (Fin 2))).mapCocone
        (colimit.cocone prodColimitSpan)).ι.app WalkingSpan.right
        ((TopCat.prodIsoProd (TopCat.of (Fin 2)) (TopCat.of (Fin 3))).inv
          ((1 : Fin 2), (2 : Fin 3)))) = (1 : Fin 2) ∧
    (Limits.prod.snd : TopCat.of (Fin 2) ⨯ (colimit.cocone prodColimitSpan).pt ⟶
      (colimit.cocone prodColimitSpan).pt)
      (((Limits.prod.functor.obj (TopCat.of (Fin 2))).mapCocone
        (colimit.cocone prodColimitSpan)).ι.app WalkingSpan.right
        ((TopCat.prodIsoProd (TopCat.of (Fin 2)) (TopCat.of (Fin 3))).inv
          ((1 : Fin 2), (2 : Fin 3)))) =
      (colimit.cocone prodColimitSpan).ι.app WalkingSpan.right (2 : Fin 3) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨isColimitOfPreserves _ (colimit.isColimit _)⟩
  · have hmap : (((Limits.prod.functor.obj (TopCat.of (Fin 2))).mapCocone
          (colimit.cocone prodColimitSpan)).ι.app WalkingSpan.right)
          ((TopCat.prodIsoProd (TopCat.of (Fin 2)) (TopCat.of (Fin 3))).inv
            ((1 : Fin 2), (2 : Fin 3))) =
        (Limits.prod.map (𝟙 (TopCat.of (Fin 2)))
          ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right))
        ((TopCat.prodIsoProd (TopCat.of (Fin 2)) (TopCat.of (Fin 3))).inv
          ((1 : Fin 2), (2 : Fin 3))) := rfl
    have htrans := TopCat.prodMap_prodIso_inv_apply
      (K := TopCat.of (Fin 2))
      ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right)
      (1 : Fin 2) (2 : Fin 3)
    have hFst : (Limits.prod.fst : TopCat.of (Fin 2) ⨯
          (colimit.cocone prodColimitSpan).pt ⟶ TopCat.of (Fin 2))
        ((TopCat.prodIsoProd (TopCat.of (Fin 2))
          (colimit.cocone prodColimitSpan).pt).inv
          ((1 : Fin 2),
            ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right)
              (2 : Fin 3))) = (1 : Fin 2) :=
      ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_fst (TopCat.of (Fin 2))
          (colimit.cocone prodColimitSpan).pt)
        ((1 : Fin 2),
          ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right)
            (2 : Fin 3))
    exact ((congrArg _ hmap).trans ((congrArg _ htrans).trans hFst))
  · have hmap : (((Limits.prod.functor.obj (TopCat.of (Fin 2))).mapCocone
          (colimit.cocone prodColimitSpan)).ι.app WalkingSpan.right)
          ((TopCat.prodIsoProd (TopCat.of (Fin 2)) (TopCat.of (Fin 3))).inv
            ((1 : Fin 2), (2 : Fin 3))) =
        (Limits.prod.map (𝟙 (TopCat.of (Fin 2)))
          ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right))
        ((TopCat.prodIsoProd (TopCat.of (Fin 2)) (TopCat.of (Fin 3))).inv
          ((1 : Fin 2), (2 : Fin 3))) := rfl
    have htrans := TopCat.prodMap_prodIso_inv_apply
      (K := TopCat.of (Fin 2))
      ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right)
      (1 : Fin 2) (2 : Fin 3)
    have hSnd : (Limits.prod.snd : TopCat.of (Fin 2) ⨯
          (colimit.cocone prodColimitSpan).pt ⟶
          (colimit.cocone prodColimitSpan).pt)
        ((TopCat.prodIsoProd (TopCat.of (Fin 2))
          (colimit.cocone prodColimitSpan).pt).inv
          ((1 : Fin 2),
            ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right)
              (2 : Fin 3))) =
        ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right)
          (2 : Fin 3) :=
      ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_snd (TopCat.of (Fin 2))
          (colimit.cocone prodColimitSpan).pt)
        ((1 : Fin 2),
          ((colimit.cocone prodColimitSpan).ι.app WalkingSpan.right)
            (2 : Fin 3))
    exact ((congrArg _ hmap).trans ((congrArg _ htrans).trans hSnd))

#print axioms prodColimit_pushout_fixedLeft_right_leg

end MathlibExtTest.Topology.Category.TopCat.ProdColimitTests
