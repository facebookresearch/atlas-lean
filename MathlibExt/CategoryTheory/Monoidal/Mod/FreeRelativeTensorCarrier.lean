/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.FreeRelativeTensor

/-!
# The original free relative tensor carrier in complement-first order

The isomorphism is the actual relative coequalizer contraction, followed by
the original ambient braid. Its generator is the unchanged free-adjunction
unit and balancing projection. No collapse is supplied as an assumption.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.FreeRelativeTensorCarrier

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : CommMon C)

/-- The entire original balanced free carrier is the complement-first
ambient tensor, with the same chosen coequalizer and both actual maps. -/
def carrierIso (P : C) (N : Mod C A.X) :
    (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N).X ≅ N.X ⊗ P :=
  FreeRelativeTensor.underlyingIso A P N ≪≫ β_ P N.X

/-- The whole generator leg is the actual original free unit followed by
the relative balancing projection. -/
def generator (P : C) (N : Mod C A.X) :
    P ⊗ N.X ⟶ (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N).X :=
  FreeRelativeTensor.inverseRaw A P N

/-- The full free generator is mapped to the actual ambient braid. -/
@[reassoc]
theorem generator_carrierIso (P : C) (N : Mod C A.X) :
    generator A P N ≫ (carrierIso A P N).hom = (β_ P N.X).hom := by
  let e := FreeRelativeTensor.underlyingIso A P N
  change FreeRelativeTensor.inverseRaw A P N ≫
    (e.hom ≫ (β_ P N.X).hom) = _
  have h : FreeRelativeTensor.inverseRaw A P N ≫ e.hom = 𝟙 _ := e.inv_hom_id
  exact (Category.assoc (FreeRelativeTensor.inverseRaw A P N) e.hom
      (β_ P N.X).hom).symm.trans
    ((congrArg (fun f => f ≫ (β_ P N.X).hom) h).trans (Category.id_comp _))

/-- The same complete comparison retains both original coefficient and
target maps in the complement-first tensor order. -/
theorem carrierIso_naturality {P Q : C} (f : P ⟶ Q)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    (Mod.relativeTensorMap A ((Mod.free A.X).map f) g).hom ≫
        (carrierIso A Q N').hom =
      (carrierIso A P N).hom ≫ (g.hom ⊗ₘ f) := by
  let t := (Mod.relativeTensorMap A ((Mod.free A.X).map f) g).hom
  let e := (FreeRelativeTensor.underlyingIso A P N).hom
  let e' := (FreeRelativeTensor.underlyingIso A Q N').hom
  let b := f ⊗ₘ g.hom
  have he : t ≫ e' = e ≫ b := FreeRelativeTensor.coefficient_naturality A f g
  have hb : b ≫ (β_ Q N'.X).hom = (β_ P N.X).hom ≫ (g.hom ⊗ₘ f) :=
    braiding_naturality f g.hom
  change t ≫ (e' ≫ (β_ Q N'.X).hom) =
    (e ≫ (β_ P N.X).hom) ≫ (g.hom ⊗ₘ f)
  rw [← Category.assoc, he, Category.assoc, hb, ← Category.assoc]

end CategoryTheory.Mod.FreeRelativeTensorCarrier
