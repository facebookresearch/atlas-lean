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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositiveHomotopyGluing

/-!
# Homotopy classes of CP-contractive asymptotic morphisms

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Constant paths, interval reversal and concatenation preserve complete positivity and
contractivity. Homotopy is therefore an equivalence relation, and its quotient is
CompletelyPositiveContraction.HomotopyClasses A B.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace AsymptoticMorphism
namespace CompletelyPositiveContraction

open ContinuousMap.IntervalGluing

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {phi psi chi : CompletelyPositiveContraction A B}

namespace Homotopy

/-- **CP-contractive homotopies are determined by their families.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. If H,K are homotopies from φ to ψ with H.family=K.family as CP-contractive
interval-valued families, then H=K.
-/
@[ext]
theorem ext {H K : Homotopy phi psi} (h : H.family = K.family) : H = K := by
  cases H
  cases K
  cases h
  rfl

/-- **Constant CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. The homotopy refl φ from φ to
itself has values F_t(a)(s)=φ_t(a) for s∈[0,1].
-/
noncomputable def refl
    (phi : CompletelyPositiveContraction A B) : Homotopy phi phi where
  family := phi.postcomp (constantHom B)
  start := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply, constantHom_apply]
  finish := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply, constantHom_apply]

/-- **Reversal of a CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. The homotopy symm H from ψ to φ has values H_t(a)(1-s).
-/
noncomputable def symm (H : Homotopy phi psi) : Homotopy psi phi where
  family := H.family.postcomp (reverseHom B)
  start := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply, reverseHom_zero]
    exact H.finish t a
  finish := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply, reverseHom_one]
    exact H.start t a

/-- **Concatenation of CP-contractive homotopies.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Let H be a CP-contractive homotopy from φ to ψ and K one from ψ to χ. Their pair
M_t(a)=(H_t(a),K_t(a)) lies in MatchingPaths B={(F,G)∈C([0,1],B)²:F(1)=G(0)}, with norm
max(‖F‖∞,‖G‖∞). Its glued path is F_t(a)(s)=H_t(a)(2s) for s≤1/2 and F_t(a)(s)=K_t(a)(2s-1)
for s>1/2, with common value ψ_t(a) at the midpoint. The homotopy trans H K joins φ to χ with
this CP-contractive interval-valued family.
-/
noncomputable def trans
    (H : Homotopy phi psi) (K : Homotopy psi chi) : Homotopy phi chi where
  family :=
    { toAsymptoticMorphism :=
        (H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).family
      completelyPositiveContraction :=
        trans_family_isCompletelyPositiveContraction H K }
  start := (H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).start
  finish := (H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).finish

/-- **Underlying constant asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. The ordinary asymptotic homotopy
underlying CompletelyPositiveContraction.Homotopy.refl φ equals
AsymptoticMorphism.Homotopy.refl φ.toAsymptoticMorphism, with constant interval value φ_t(a).
-/
@[simp]
theorem refl_toAsymptoticHomotopy
    (phi : CompletelyPositiveContraction A B) :
    (refl phi).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.refl
        phi.toAsymptoticMorphism := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

/-- **Underlying reversed asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. The ordinary asymptotic homotopy underlying symm H equals
AsymptoticMorphism.Homotopy.symm H.toAsymptoticHomotopy, both having values H_t(a)(1-s).
-/
@[simp]
theorem symm_toAsymptoticHomotopy (H : Homotopy phi psi) :
    (symm H).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.symm
        H.toAsymptoticHomotopy := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

/-- **Underlying concatenated asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Let H be a CP-contractive homotopy from φ to ψ and K one from ψ to χ. Their pair
M_t(a)=(H_t(a),K_t(a)) lies in MatchingPaths B={(F,G)∈C([0,1],B)²:F(1)=G(0)}, with norm
max(‖F‖∞,‖G‖∞). Its glued path is F_t(a)(s)=H_t(a)(2s) for s≤1/2 and F_t(a)(s)=K_t(a)(2s-1)
for s>1/2, with common value ψ_t(a) at the midpoint. The ordinary asymptotic homotopy
underlying trans H K equals AsymptoticMorphism.Homotopy.trans H.toAsymptoticHomotopy
K.toAsymptoticHomotopy.
-/
@[simp]
theorem trans_toAsymptoticHomotopy
    (H : Homotopy phi psi) (K : Homotopy psi chi) :
    (trans H K).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.trans
        H.toAsymptoticHomotopy K.toAsymptoticHomotopy := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

end Homotopy

/-- **Reflexivity of CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Every CP-contractive asymptotic family φ is homotopic to itself through the constant
interval path.
-/
theorem homotopic_refl (phi : CompletelyPositiveContraction A B) :
    Homotopic phi phi :=
  ⟨Homotopy.refl phi⟩

/-- **Symmetry of CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. If φ is CP-contractively homotopic to ψ, then ψ is CP-contractively homotopic to φ.
-/
theorem homotopic_symm {phi psi : CompletelyPositiveContraction A B}
    (h : Homotopic phi psi) : Homotopic psi phi := by
  rcases h with ⟨H⟩
  exact ⟨H.symm⟩

/-- **Transitivity of CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. If φ is CP-contractively homotopic to ψ and ψ to χ, then φ is CP-contractively
homotopic to χ.
-/
theorem homotopic_trans {phi psi chi : CompletelyPositiveContraction A B}
    (hphi : Homotopic phi psi) (hpsi : Homotopic psi chi) :
    Homotopic phi chi := by
  rcases hphi with ⟨H⟩
  rcases hpsi with ⟨K⟩
  exact ⟨H.trans K⟩

/-- **CP-contractive homotopy is an equivalence relation.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. The relation Homotopic on CompletelyPositiveContraction A B is reflexive, symmetric
and transitive.
-/
theorem homotopic_equivalence
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Equivalence (Homotopic :
      CompletelyPositiveContraction A B →
      CompletelyPositiveContraction A B → Prop) :=
  { refl := homotopic_refl
    symm := homotopic_symm
    trans := homotopic_trans }

/-- **Setoid of CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. The setoid CompletelyPositiveContraction.homotopySetoid A B has relation Homotopic φ
ψ, meaning that a CP-contractive interval-valued homotopy with these endpoints exists.
-/
def homotopySetoid
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (CompletelyPositiveContraction A B) where
  r := Homotopic
  iseqv := homotopic_equivalence A B

/-- **Quotient of CP-contractive families by homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. CompletelyPositiveContraction.HomotopyClasses A B is the quotient of
CompletelyPositiveContraction A B by this homotopy relation.
-/
abbrev HomotopyClasses
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  Quotient (homotopySetoid A B)

/-- **Homotopy class of a CP-contractive family.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. The map CompletelyPositiveContraction.mkClass sends φ to its class under
CP-contractive homotopy.
-/
def mkClass (phi : CompletelyPositiveContraction A B) :
    HomotopyClasses A B :=
  Quotient.mk _ phi

/-- **Equality of CP-contractive classes is homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. For CP-contractive asymptotic morphisms φ,ψ, mkClass φ=mkClass ψ if and only if
Homotopic φ ψ.
-/
@[simp]
theorem mkClass_eq_mkClass_iff
    (phi psi : CompletelyPositiveContraction A B) :
    mkClass phi = mkClass psi ↔ Homotopic phi psi := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

end CompletelyPositiveContraction
end AsymptoticMorphism
