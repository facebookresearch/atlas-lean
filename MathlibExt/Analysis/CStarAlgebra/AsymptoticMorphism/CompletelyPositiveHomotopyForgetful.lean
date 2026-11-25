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
# From CP-contractive to ordinary asymptotic homotopy classes

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Let Qcp(A,B) be the quotient of CP-contractive asymptotic morphisms by homotopies
through CP-contractive interval-valued families, and Qraw(A,B) the quotient of all asymptotic
star morphisms by their interval-valued asymptotic homotopies. The map
forgetClass:Qcp(A,B)→Qraw(A,B) sends the class of a CP-contractive family to the ordinary
asymptotic homotopy class of the same coefficient functions.
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

/-- **Underlying asymptotic homotopy class of a CP-contractive class.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Let Qcp(A,B) be the quotient of CP-contractive asymptotic morphisms by homotopies
through CP-contractive interval-valued families, and Qraw(A,B) the quotient of all asymptotic
star morphisms by their interval-valued asymptotic homotopies. The map forgetClass sends
[φ]∈Qcp(A,B) to the class of φ.toAsymptoticMorphism in Qraw(A,B).
-/
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

/-- **Value of the forgetful class map on a representative.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Let Qcp(A,B) be the quotient of CP-contractive asymptotic morphisms by homotopies
through CP-contractive interval-valued families, and Qraw(A,B) the quotient of all asymptotic
star morphisms by their interval-valued asymptotic homotopies. For a CP-contractive family φ,
forgetClass(mkClass φ)=AsymptoticMorphism.mkClass φ.toAsymptoticMorphism.
-/
@[simp]
theorem forgetClass_mkClass
    (phi : CompletelyPositiveContraction A B) :
    forgetClass (mkClass phi) =
      _root_.AsymptoticMorphism.mkClass phi.toAsymptoticMorphism :=
  rfl

end CompletelyPositiveContraction
end AsymptoticMorphism
