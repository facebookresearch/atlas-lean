/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleGeometry

/-!
# Native small-etale base-change identity and composition

These are the existing Over.pullbackId and Over.pullbackComp isomorphisms,
lifted through the fully faithful small-etale forgetful functor. They are
completed ordinary category/geometry maps, with no new Wanted payload.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.EtaleBaseChangeCoherence
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
universe u

/-- The actual native identity base-change comparison. -/
def identity (X : Scheme.{u}) : etaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents
    (fun U => (Scheme.Etale.forgetFullyFaithful X).preimageIso
      ((Over.pullbackId (X := X)).app ((Scheme.Etale.forget X).obj U)))
    (by
      intro U V a
      apply (Scheme.Etale.forget X).map_injective
      exact (Over.pullbackId (X := X)).hom.naturality ((Scheme.Etale.forget X).map a))

/-- Composition is the actual universal scheme pullback comparison. -/
def composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange g ⋙ etaleBaseChange f ≅ etaleBaseChange (f ≫ g) :=
  NatIso.ofComponents
    (fun U => (Scheme.Etale.forgetFullyFaithful X).preimageIso
      ((Over.pullbackComp f g).symm.app ((Scheme.Etale.forget Z).obj U)))
    (by
      intro U V a
      apply (Scheme.Etale.forget X).map_injective
      exact (Over.pullbackComp f g).symm.hom.naturality ((Scheme.Etale.forget Z).map a))

end MathlibExt.AlgebraicGeometry.EtaleBaseChangeCoherence
