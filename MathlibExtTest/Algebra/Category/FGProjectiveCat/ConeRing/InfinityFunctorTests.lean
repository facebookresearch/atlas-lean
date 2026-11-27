/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ConeRing.InfinityFunctor

/-!
# Original projective infinity functor clients

The clients use arbitrary rings, original projective objects and actual
coefficient maps. The return equations are tested on their original
elements, including the whole native infinity object.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory

universe uR

private theorem originalPairReturn {R : Type uR} [Ring R]
    {X Y : FGProjectiveCat.{uR} R} (a : X ⟶ Y) (b : Y ⟶ X)
    (h : a ≫ b = 𝟙 X) (x : X) : b.hom.hom (a.hom.hom x) = x := by
  have hl := congrArg (fun f : X ⟶ X => f.hom.hom) h
  change b.hom.hom.comp a.hom.hom = LinearMap.id at hl
  exact LinearMap.congr_fun hl x

namespace FGProjectiveCat.ConeRing.InfinityFunctorTests

variable (R : Type uR) [Ring R]

/-- The original infinity functor is additive with only the ring hypothesis. -/
theorem ring_only_additive : (infinityFunctor R).Additive := by infer_instance

/-- Its exactness is the original projective split exactness for arbitrary rings. -/
theorem ring_only_exact : (infinityFunctor R).IsExact := by infer_instance

/-- The original first insertion and extraction return every original module element. -/
theorem first_return (X : category R) (x : X) :
    ((extract R).app X).hom.hom (((insert R).app X).hom.hom x) = x := by
  have h : (insert R).app X ≫ (extract R).app X = 𝟙 X :=
    congrArg (fun η => η.app X) (insert_extract R)
  exact originalPairReturn ((insert R).app X) ((extract R).app X) h x

/-- The original tail projection and inclusion return every original infinity element. -/
theorem tail_return (X : category R) (x : (infinityFunctor R).obj X) :
    ((tailInclusionMap R).app X).hom.hom
        (((tailProjectionMap R).app X).hom.hom x) = x := by
  have h : (tailProjectionMap R).app X ≫ (tailInclusionMap R).app X =
      𝟙 ((infinityFunctor R).obj X) :=
    congrArg (fun η => η.app X) (tailProjectionMap_tailInclusionMap R)
  exact originalPairReturn ((tailProjectionMap R).app X) ((tailInclusionMap R).app X) h x

/-- The actual mixed row remains zero on the original functor objects. -/
theorem mixed_row (X : category R) :
    (tailProjectionMap R).app X ≫ (extract R).app X = 0 :=
  congrArg (fun η => η.app X) (tailProjectionMap_extract R)

end FGProjectiveCat.ConeRing.InfinityFunctorTests

end
