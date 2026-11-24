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
# Completely-positive asymptotic homotopy classes

Literal CPC homotopy is proved reflexive, symmetric and transitive by reusing
the established ordinary homotopy operations and the H2 CPC proofs. The proved
equivalence then defines the actual Setoid and quotient.
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

/-- A CPC homotopy is determined by its actual CPC family; endpoint fields are
proofs. -/
@[ext]
theorem ext {H K : Homotopy phi psi} (h : H.family = K.family) : H = K := by
  cases H
  cases K
  cases h
  rfl

/-- Literal constant-in-homotopy-parameter CPC homotopy. -/
noncomputable def refl
    (phi : CompletelyPositiveContraction A B) : Homotopy phi phi where
  family := phi.postcomp (constantHom B)
  start := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply, constantHom_apply]
  finish := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply, constantHom_apply]

/-- Reverse the interval parameter of a CPC homotopy. -/
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

/-- Concatenate CPC homotopies using the exact existing ordinary trans family
and its proved H2 CPC property. -/
noncomputable def trans
    (H : Homotopy phi psi) (K : Homotopy psi chi) : Homotopy phi chi where
  family :=
    { toAsymptoticMorphism :=
        (H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).family
      completelyPositiveContraction :=
        trans_family_isCompletelyPositiveContraction H K }
  start := (H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).start
  finish := (H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).finish

/-- CPC reflexivity forgets to the established ordinary reflexivity homotopy. -/
@[simp]
theorem refl_toAsymptoticHomotopy
    (phi : CompletelyPositiveContraction A B) :
    (refl phi).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.refl
        phi.toAsymptoticMorphism := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

/-- CPC symmetry forgets to the established ordinary reversed homotopy. -/
@[simp]
theorem symm_toAsymptoticHomotopy (H : Homotopy phi psi) :
    (symm H).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.symm
        H.toAsymptoticHomotopy := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

/-- CPC transitivity forgets to the established ordinary concatenated
homotopy. -/
@[simp]
theorem trans_toAsymptoticHomotopy
    (H : Homotopy phi psi) (K : Homotopy psi chi) :
    (trans H K).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.trans
        H.toAsymptoticHomotopy K.toAsymptoticHomotopy := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

end Homotopy

/-- CPC homotopy is reflexive. -/
theorem homotopic_refl (phi : CompletelyPositiveContraction A B) :
    Homotopic phi phi :=
  ⟨Homotopy.refl phi⟩

/-- CPC homotopy is symmetric. -/
theorem homotopic_symm {phi psi : CompletelyPositiveContraction A B}
    (h : Homotopic phi psi) : Homotopic psi phi := by
  rcases h with ⟨H⟩
  exact ⟨H.symm⟩

/-- CPC homotopy is transitive. -/
theorem homotopic_trans {phi psi chi : CompletelyPositiveContraction A B}
    (hphi : Homotopic phi psi) (hpsi : Homotopic psi chi) :
    Homotopic phi chi := by
  rcases hphi with ⟨H⟩
  rcases hpsi with ⟨K⟩
  exact ⟨H.trans K⟩

/-- The literal CPC homotopy relation is an equivalence relation. -/
theorem homotopic_equivalence
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Equivalence (Homotopic :
      CompletelyPositiveContraction A B →
      CompletelyPositiveContraction A B → Prop) :=
  { refl := homotopic_refl
    symm := homotopic_symm
    trans := homotopic_trans }

/-- Actual Setoid of CPC asymptotic families under literal CPC homotopy. -/
def homotopySetoid
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (CompletelyPositiveContraction A B) where
  r := Homotopic
  iseqv := homotopic_equivalence A B

/-- Actual homotopy classes of finite-time CPC asymptotic families. -/
abbrev HomotopyClasses
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  Quotient (homotopySetoid A B)

/-- Class of a literal CPC asymptotic family. -/
def mkClass (phi : CompletelyPositiveContraction A B) :
    HomotopyClasses A B :=
  Quotient.mk _ phi

/-- Equality of CPC classes is exactly literal CPC homotopy. -/
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
