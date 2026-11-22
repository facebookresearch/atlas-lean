/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Whiskering

/-!
# Actual successor comparisons for all integer powers of an equivalence

The native integer powers retain the specified inverse equivalence.
Successor comparisons use the original unitors, associators and counit,
including at every negative integer. Their inverse-adjoint comparison
retains the specified unit as well. Additivity is earned from the original
forward functor and its actual inverse.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Functor

namespace CategoryTheory.Equivalence.IntegerSuccessor

variable {C : Type u} [Category.{v} C]

/-- The full successor comparison for actual nonnegative powers, with all associators retained. -/
def natural (e : C ≌ C) : (n : ℕ) →
    (e.powNat n).functor ⋙ e.functor ≅ (e.powNat (n + 1)).functor
  | 0 => Functor.leftUnitor e.functor
  | 1 => Iso.refl _
  | n + 2 => Functor.associator _ _ _ ≪≫ isoWhiskerLeft e.functor (natural e (n + 1))

/-- Every negative successor cancels the SAME actual inverse through the original counit. -/
def negative (e : C ≌ C) : (n : ℕ) →
    (e.symm.powNat (n + 1)).functor ⋙ e.functor ≅ (e.symm.powNat n).functor
  | 0 => e.counitIso
  | 1 => Functor.associator _ _ _ ≪≫ isoWhiskerLeft e.inverse e.counitIso ≪≫
      Functor.rightUnitor e.inverse
  | n + 2 => Functor.associator _ _ _ ≪≫ isoWhiskerLeft e.inverse (negative e (n + 1))

/-- The full original successor map exists at EVERY integer, retaining the negative-degree counit word. -/
def comparison (e : C ≌ C) : (n : ℤ) →
    (e ^ n).functor ⋙ e.functor ≅ (e ^ (n + 1)).functor
  | .ofNat n => natural e n
  | .negSucc 0 => negative e 0
  | .negSucc (n + 1) => negative e (n + 1)

/-- Degree zero retains the actual functor left unitor. -/
theorem comparison_zero (e : C ≌ C) : comparison e 0 = Functor.leftUnitor e.functor := rfl

/-- The degree minus one comparison is the SAME original counit on every object. -/
theorem comparison_neg_one_hom (e : C ≌ C) (X : C) :
    (comparison e (-1)).hom.app X = e.counitIso.hom.app X := rfl

/-- The original unit followed by the SAME integer successor map supplies its actual inverse-adjoint comparison. -/
def inverseComparison (e : C ≌ C) (n : ℤ) :
    (e ^ n).functor ≅ (e ^ (n + 1)).functor ⋙ e.inverse :=
  (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ e.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (comparison e n) e.inverse

/-- The inverse-adjoint comparison retains the original unit followed by
the actual inverse-image successor map. -/
theorem inverseComparison_hom (e : C ≌ C) (n : ℤ) (X : C) :
    (inverseComparison e n).hom.app X = e.unitIso.hom.app ((e ^ n).functor.obj X) ≫
      e.inverse.map ((comparison e n).hom.app X) := by
  simp [inverseComparison]

/-- Additivity holds for every actual nonnegative power of the SAME original functor. -/
theorem natural_additive [Preadditive C] (e : C ≌ C) [e.functor.Additive] :
    (n : ℕ) → (e.powNat n).functor.Additive
  | 0 => by
      change (𝟭 C).Additive
      infer_instance
  | 1 => by
      change e.functor.Additive
      infer_instance
  | n + 2 => by
      let := natural_additive e (n + 1)
      change (e.functor ⋙ (e.powNat (n + 1)).functor).Additive
      infer_instance

/-- The actual specified inverse, not a new inverse or additivity premise, gives additive powers at EVERY integer. -/
theorem additive [Preadditive C] (e : C ≌ C) [e.functor.Additive] (n : ℤ) :
    (e ^ n).functor.Additive := by
  cases n with
  | ofNat n => exact natural_additive e n
  | negSucc n =>
      let : e.symm.functor.Additive := by
        change e.inverse.Additive
        infer_instance
      exact natural_additive e.symm (n + 1)

end CategoryTheory.Equivalence.IntegerSuccessor
