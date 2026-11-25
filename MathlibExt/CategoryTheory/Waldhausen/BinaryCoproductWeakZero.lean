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

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductFunctor
public import MathlibExt.CategoryTheory.Waldhausen.Gluing
public import MathlibExt.CategoryTheory.Products.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Zero and weak preservation of the actual Waldhausen coproduct functor

The coproduct of two zero objects is zero by its colimit universal
property. The genuine original gluing axiom applied to the two zero
pushout squares proves weak preservation of the actual coproduct map.
Both statements transfer to the original functor through its earned
object isomorphisms.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The actual derived coproduct of two zero objects is zero. -/
theorem binaryCoproductColimitCocone_isZero (X Y : C) (hX : IsZero X) (hY : IsZero Y) :
    IsZero (binaryCoproductColimitCocone C (pair X Y)).cocone.pt := by
  let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone
  let : IsIso c.inl :=
    (BinaryCofan.isColimit_iff_isIso_inl hY.isInitial c).mp
      ⟨(binaryCoproductColimitCocone C (pair X Y)).isColimit⟩
  exact hX.of_iso (asIso c.inl).symm

/-- The actual coproduct functor carries every zero pair to a zero object. -/
theorem waldhausenCoproductFunctor_obj_isZero (p : C × C) (hp : IsZero p) :
    IsZero ((waldhausenCoproductFunctor C).obj p) := by
  have hparts := (isZero_prod_iff (C := C) (D := C)).mp hp
  exact (binaryCoproductColimitCocone_isZero C p.1 p.2 hparts.1 hparts.2).of_iso
    (eqToIso (waldhausenCoproductFunctor_obj C p))

/-- Original component weak equivalences give a weak equivalence of the
actual coproduct apices by the original Waldhausen gluing axiom. -/
theorem binaryCoproductMap_isWeakEquivalence (hG : WaldhausenGluingAxiom (C := C))
    {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : IsWeakEquivalence f) (hg : IsWeakEquivalence g) :
    IsWeakEquivalence (binaryCoproductMap C f g) := by
  let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone
  let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone
  have hp : IsPushout ((isZero_zero C).isInitial.to X) ((isZero_zero C).isInitial.to Y)
      c.inl c.inr :=
    IsPushout.of_is_coproduct (binaryCoproductColimitCocone C (pair X Y)).isColimit
      (isZero_zero C).isInitial
  have hp' : IsPushout ((isZero_zero C).isInitial.to X') ((isZero_zero C).isInitial.to Y')
      c'.inl c'.inr :=
    IsPushout.of_is_coproduct (binaryCoproductColimitCocone C (pair X' Y')).isColimit
      (isZero_zero C).isInitial
  exact hG.gluing hp hp' (𝟙 (0 : C)) f g (binaryCoproductMap C f g)
    (WaldhausenCategoryWithoutGluing.zero_isCofibration X _)
    (WaldhausenCategoryWithoutGluing.zero_isCofibration X' _)
    ((isZero_zero C).eq_of_src _ _) ((isZero_zero C).eq_of_src _ _)
    (binaryCoproductMap_inl C f g) (binaryCoproductMap_inr C f g)
    ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso (𝟙 (0 : C))) hf hg

/-- The original coproduct functor preserves component weak equivalences
through its whole map transports, under the genuine base gluing axiom. -/
theorem waldhausenCoproductFunctor_map_isWeakEquivalence
    (hG : WaldhausenGluingAxiom (C := C)) {p q : C × C} (f : p ⟶ q)
    (hf : IsWeakEquivalence f.1) (hg : IsWeakEquivalence f.2) :
    IsWeakEquivalence ((waldhausenCoproductFunctor C).map f) := by
  rw [waldhausenCoproductFunctor_map]
  refine (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).comp_mem _ _
    ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso _) ?_
  exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).comp_mem _ _
    (binaryCoproductMap_isWeakEquivalence C hG f.1 f.2 hf hg)
    ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso _)

end CategoryTheory.Waldhausen
