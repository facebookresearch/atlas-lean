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

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# The literal Waldhausen approximation property

This file packages Weibel's displayed approximation property `(App)`: a map
out of an object in the image factors through another image object followed
by a weak equivalence.  Crucially, the source map is arbitrary.  A
cofibration replacement requires separate mapping-cylinder hypotheses and is
not part of this carrier.

Reflection of weak equivalences is a separate proposition, as is explicit
Waldhausen exactness.  No typeclass, global instance, cylinder, Stage map,
comma contraction, realization result, or K-theory theorem is introduced.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E]
variable [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]
  [WaldhausenCategoryWithoutGluing E]
variable {F : C ⥤ D} {G : D ⥤ E}

/-- The literal Waldhausen approximation property `(App)`.

The source map `a` is deliberately not required to be a cofibration. -/
structure WaldhausenApproximationProperty (F : C ⥤ D) : Prop where
  /-- Factor a map out of an image through an arbitrary source map followed
  by a weak equivalence. -/
  factorization : ∀ (X : C) (Y : D) (g : F.obj X ⟶ Y),
    ∃ (Xnext : C) (a : X ⟶ Xnext) (p : F.obj Xnext ⟶ Y),
      IsWeakEquivalence p ∧ F.map a ≫ p = g

namespace WaldhausenApproximationProperty

/-- The identity functor satisfies the literal approximation property. -/
protected theorem id :
    (Functor.id C).WaldhausenApproximationProperty where
  factorization X Y g :=
    ⟨Y, g, 𝟙 Y,
      (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).id_mem Y, by simp⟩

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- Literal approximation properties compose when the second functor
explicitly preserves weak equivalences. -/
theorem comp (hF : F.WaldhausenApproximationProperty)
    (hG : G.WaldhausenApproximationProperty)
    (hGExact : G.IsWaldhausenExact) :
    (F ⋙ G).WaldhausenApproximationProperty where
  factorization X Z g := by
    obtain ⟨Y, b, q, hq, hg⟩ := hG.factorization (F.obj X) Z g
    obtain ⟨Xnext, a, p, hp, hb⟩ := hF.factorization X Y b
    refine ⟨Xnext, a, G.map p ≫ q, ?_, ?_⟩
    · exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := E)).comp_mem _ _
        (hGExact.map_weakEquivalence p hp) hq
    · change G.map (F.map a) ≫ (G.map p ≫ q) = g
      calc
        _ = G.map (F.map a ≫ p) ≫ q := by
          rw [G.map_comp, Category.assoc]
        _ = G.map b ≫ q := by rw [hb]
        _ = g := hg

end WaldhausenApproximationProperty

/-- A functor reflects Waldhausen weak equivalences.

This proposition is intentionally separate from
`WaldhausenApproximationProperty` and is not a typeclass. -/
def ReflectsWaldhausenWeakEquivalences (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    IsWeakEquivalence (F.map f) → IsWeakEquivalence f

end CategoryTheory.Functor

end
