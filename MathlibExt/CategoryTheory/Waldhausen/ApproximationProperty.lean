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
# Waldhausen approximation factorization

For a functor F:C → D into a category with Waldhausen weak-equivalence
data, the approximation factorization condition (App) says that every
g:F(X) → Y factors as F(X) —F(a)→ F(X′) —p→ Y, where p is a weak
equivalence and a:X → X′ is an arbitrary source map.

The identity satisfies this condition. Two such factorizations compose when
the second functor is Waldhausen exact. Reflection of weak equivalences is
the condition F(f) weak implies f weak, considered independently of the
factorization condition.
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

/-- Let C be a category and D a category with a zero object and Waldhausen
cofibration, weak-equivalence and pushout axioms.
For F:C → D, the approximation factorization property requires every
g:F(X) → Y to factor as p∘F(a), with a:X → X′ an arbitrary map
and p:F(X′) → Y a weak equivalence. -/
structure WaldhausenApproximationProperty (F : C ⥤ D) : Prop where
  /-- For a functor F:C → D satisfying the Waldhausen approximation
factorization property, every g:F(X) → Y admits X′, a:X → X′
and a weak equivalence p:F(X′) → Y such that p∘F(a)=g. -/
  factorization : ∀ (X : C) (Y : D) (g : F.obj X ⟶ Y),
    ∃ (Xnext : C) (a : X ⟶ Xnext) (p : F.obj Xnext ⟶ Y),
      IsWeakEquivalence p ∧ F.map a ≫ p = g

namespace WaldhausenApproximationProperty

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms.

The identity functor of C satisfies the approximation factorization property. -/
protected theorem id :
    (Functor.id C).WaldhausenApproximationProperty where
  factorization X Y g :=
    ⟨Y, g, 𝟙 Y,
      (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).id_mem Y, by simp⟩

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- Let C be a category, D,E have zero objects and Waldhausen
cofibration/weak-equivalence data, and F:C → D, G:D → E satisfy
the approximation factorization property. If G is Waldhausen exact,
then G∘F also satisfies the approximation factorization property. -/
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

/-- Let C,D have zero objects and Waldhausen cofibration/weak-equivalence
data, and F:C → D be a functor. Reflection of weak equivalences is
the property that, for every f:X → Y, weak equivalence of F(f)
implies weak equivalence of f. -/
def ReflectsWaldhausenWeakEquivalences (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    IsWeakEquivalence (F.map f) → IsWeakEquivalence f

end CategoryTheory.Functor

end
