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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositiveHomotopyEquivalence

/-!
# Forgetting CPC evidence on asymptotic homotopy classes

The existing family and whole homotopy forgetful maps descend directly through
the proved CPC homotopy Setoid.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AsymptoticMorphism
namespace CompletelyPositiveContraction

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Forget finite-time CPC evidence from an actual CPC homotopy class. -/
def forgetClass :
    HomotopyClasses A B →
      _root_.AsymptoticMorphism.HomotopyClasses A B :=
  Quotient.map
    (sa := homotopySetoid A B)
    (sb := _root_.AsymptoticMorphism.homotopySetoid A B)
    (fun phi => phi.toAsymptoticMorphism) (by
      intro phi psi h
      rcases h with ⟨H⟩
      exact ⟨H.toAsymptoticHomotopy⟩)

/-- The forgetful class map sends a CPC class constructor to the ordinary class
of its underlying family. -/
@[simp]
theorem forgetClass_mkClass
    (phi : CompletelyPositiveContraction A B) :
    forgetClass (mkClass phi) =
      _root_.AsymptoticMorphism.mkClass phi.toAsymptoticMorphism :=
  rfl

end CompletelyPositiveContraction
end AsymptoticMorphism
