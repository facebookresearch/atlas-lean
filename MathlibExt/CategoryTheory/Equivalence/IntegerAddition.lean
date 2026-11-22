/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Equivalence.IntegerCoherentShift
public import Lean.Elab.Tactic.Omega

/-!
# Original integer equivalence powers and their addition maps

The actual native powers and the specified inverse are retained. Their
source-built orbit shift supplies coherent addition, including both unit
laws and associativity. Inverse comparisons use the original successor,
unit and counit. No unrelated functor family or addition map is an input.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory Functor

namespace CategoryTheory.Equivalence.IntegerAddition

variable {C : Type u} [Category.{v} C]

/-- Appending the specified inverse uses the same original unit and successor comparison. -/
def predecessor (e : C ≌ C) (n : ℤ) :
    (e ^ n).functor ⋙ e.inverse ≅ (e ^ (n - 1)).functor :=
  isoWhiskerRight
      (eqToIso (congrArg (fun k : ℤ => (e ^ k).functor) (show n = (n - 1) + 1 by omega)))
      e.inverse ≪≫
    (IntegerSuccessor.inverseComparison e (n - 1)).symm

/-- Every original integer pair has the complete coherent source-built addition comparison. -/
def comparison (e : C ≌ C) (n m : ℤ) :
    (e ^ n).functor ⋙ (e ^ m).functor ≅ (e ^ (n + m)).functor :=
  IntegerOrbit.nativeComparison e n m

/-- Reversing the original equivalence is precisely negating the integer degree. -/
def reversal (e : C ≌ C) : (n : ℤ) → (e ^ (-n)).functor ≅ (e.symm ^ n).functor
  | .ofNat 0 => Iso.refl _
  | .ofNat (_n + 1) => Iso.refl _
  | .negSucc _n => Iso.refl _

/-- The inverse of every native nonnegative equivalence power uses the same inverse-functor powers. -/
def naturalInverse (e : C ≌ C) : (n : ℕ) →
    (e.powNat n).inverse ≅ (e.symm.powNat n).functor
  | 0 => Iso.refl _
  | 1 => Iso.refl _
  | n + 2 => isoWhiskerRight (naturalInverse e (n + 1)) e.inverse ≪≫
      IntegerSuccessor.natural e.symm (n + 1)

/-- The actual inverse functor of every integer power agrees with the original negative degree. -/
def inversePower (e : C ≌ C) : (n : ℤ) → (e ^ n).inverse ≅ (e ^ (-n)).functor
  | .ofNat n => naturalInverse e n ≪≫ (reversal e (n : ℤ)).symm
  | .negSucc n => naturalInverse e.symm (n + 1)

/-- Every actual arrow satisfies the full forward addition square. -/
theorem comparison_naturality (e : C ≌ C) (n m : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((e ^ n).functor ⋙ (e ^ m).functor).map f ≫ (comparison e n m).hom.app Y =
      (comparison e n m).hom.app X ≫ (e ^ (n + m)).functor.map f :=
  (comparison e n m).hom.naturality f

/-- The inverse addition square retains both original functor powers and every arrow. -/
theorem comparison_inverse_naturality (e : C ≌ C) (n m : ℤ) {X Y : C} (f : X ⟶ Y) :
    (e ^ (n + m)).functor.map f ≫ (comparison e n m).inv.app Y =
      (comparison e n m).inv.app X ≫ ((e ^ n).functor ⋙ (e ^ m).functor).map f :=
  (comparison e n m).inv.naturality f

/-- Both original functor directions agree under actual degree negation. -/
theorem reversal_hom_app (e : C ≌ C) (n : ℤ) (X : C) :
    HEq ((reversal e n).hom.app X) (𝟙 ((e ^ (-n)).functor.obj X)) := by
  cases n with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

end CategoryTheory.Equivalence.IntegerAddition
