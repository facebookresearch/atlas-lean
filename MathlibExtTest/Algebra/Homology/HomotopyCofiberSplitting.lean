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


public import MathlibExt.Algebra.Homology.HomotopyCofiberSplitting

/-! Client and axiom tests for zero-source homotopy cofibers. -/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
variable {F G F' G' : HomologicalComplex C c}
variable (f : F ⟶ G) (f' : F' ⟶ G')
variable (hF : IsZero F) (hF' : IsZero F')

example : homotopyCofiber f ⟶ G :=
  zeroSourceDesc f hF

example : homotopyCofiber f ≅ G :=
  zeroSourceIso f hF

example : inr f ≫ zeroSourceDesc f hF = 𝟙 G :=
  inr_zeroSourceDesc f hF

example : zeroSourceDesc f hF ≫ inr f = 𝟙 (homotopyCofiber f) :=
  zeroSourceDesc_inr f hF

example (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    mapArrowHom f f' H a ≫ zeroSourceDesc f' hF' =
      zeroSourceDesc f hF ≫ a.right :=
  mapArrowHom_comp_zeroSourceDesc H f f' hF hF' a

#print axioms HomologicalComplex.homotopyCofiber.zeroSourceIso
#print axioms HomologicalComplex.homotopyCofiber.mapArrowHom_comp_zeroSourceDesc

end HomologicalComplex.homotopyCofiber

end
