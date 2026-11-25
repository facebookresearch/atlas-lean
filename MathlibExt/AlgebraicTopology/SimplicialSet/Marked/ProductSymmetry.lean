/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InternalHomAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Native marked product symmetry and the original left-product adjunction

Swapping the two whole original simplicial coordinates preserves exactly
their supplied marked-edge predicates. Its native natural isomorphism
transports the existing product/internal-Hom adjunction to left products.
No new internal-Hom construction or marked model is introduced.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked

/-- Swap the original product coordinates while retaining both original markings. -/
def prodSwapIso (X Y : Marked.{u}) : prod X Y ≅ prod Y X where
  hom := prodLift (prodSnd X Y) (prodFst X Y)
  inv := prodLift (prodSnd Y X) (prodFst Y X)
  hom_inv_id := Hom.ext rfl
  inv_hom_id := Hom.ext rfl

/-- The same native marked swap is natural in both original maps. -/
theorem prodSwapIso_natural {X X' Y Y' : Marked.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    prodMap f g ≫ (prodSwapIso X' Y').hom = (prodSwapIso X Y).hom ≫ prodMap g f := Hom.ext rfl

/-- The original marked left product acts by the same original second-coordinate map. -/
def prodLeft (X : Marked.{u}) : Marked.{u} ⥤ Marked.{u} where
  obj Y := prod X Y
  map f := prodMap (𝟙 X) f
  map_id Y := prodMap_id X Y
  map_comp f g := by simpa only [Category.id_comp] using prodMap_comp (𝟙 X) (𝟙 X) f g

/-- Original left and right products are naturally isomorphic by the same native coordinate swap. -/
def prodSwapNatIso (X : Marked.{u}) : prodRight X ≅ prodLeft X :=
  NatIso.ofComponents (fun Y => prodSwapIso Y X)
    (fun f => prodSwapIso_natural f (𝟙 X))

/-- The original left-product adjunction reuses the same actual marked internal-Hom functor. -/
def leftProductAdjunction (X : Marked.{u}) : prodLeft X ⊣ internalHomFunctor X :=
  (internalHomAdjunction X).ofNatIsoLeft (prodSwapNatIso X)

/-- The native original left product preserves colimits at its unchanged value-universe bound. -/
theorem prodLeft_preservesColimits (X : Marked.{u}) : PreservesColimitsOfSize.{u, u} (prodLeft X) :=
  (leftProductAdjunction X).leftAdjoint_preservesColimits

end SSet.Marked
