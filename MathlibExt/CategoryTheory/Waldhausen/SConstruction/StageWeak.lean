/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Reindex

/-!
# Pointwise stage weak equivalences

Pointwise weak equivalences on bundled finite stages `Stage C n`, as the
inverse image of pointwise weak equivalences
`WaldhausenCategoryWithoutGluing.weakEquivalences.functorCategory (Ar n)` along the
forgetful functor `forget C n`. Membership is pointwise; `IsMultiplicative` and
`RespectsIso` are inherited via generic functor-category and `inverseImage`
instances. Reindexing along a
simplex map preserves membership by transport along `indexFunctor`.

Nonclaims: no `WideSubcategory` bundle, no weak-equivalence nerve, no
realization, no two-of-three, no saturation, no gluing, no Q/S comparison, no
K-theory, no G-theory.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
  (n : ℕ)

/-- Pointwise stage weak equivalences: inverse image of pointwise weak
equivalences along `forget C n`. -/
def stageWeak : MorphismProperty (Stage C n) :=
  (WaldhausenCategoryWithoutGluing.weakEquivalences.functorCategory (Ar n)).inverseImage
      (forget C n)

/-- Abbreviation for membership in `stageWeak C n`. -/
abbrev IsStageWeak {X Y : Stage C n} (f : X ⟶ Y) : Prop :=
  stageWeak C n f

/-- Membership in `stageWeak C n` is pointwise weak equivalence at every
index `a : Ar n`. -/
@[simp]
theorem mem_stageWeak {X Y : Stage C n} {f : X ⟶ Y} :
    stageWeak C n f ↔ ∀ a, IsWeakEquivalence ((eval C n a).map f) :=
  Iff.rfl

/-- `stageWeak` is multiplicative by pointwise inheritance: identity and composition
hold at each index `a` via the underlying weak-equivalence closure. -/
instance stageWeak_isMultiplicative : (stageWeak C n).IsMultiplicative :=
  inferInstanceAs
    (((WaldhausenCategoryWithoutGluing.weakEquivalences.functorCategory (Ar n)).inverseImage
      (forget C n)).IsMultiplicative)

/-- `stageWeak` respects isomorphisms by pointwise inheritance: pre/post-composition
with an iso holds at each index `a` via iso-closure of the underlying weak equivalences
after transporting `IsIso` through `forget` and evaluation. -/
instance stageWeak_respectsIso : (stageWeak C n).RespectsIso :=
  inferInstanceAs
    (((WaldhausenCategoryWithoutGluing.weakEquivalences.functorCategory (Ar n)).inverseImage
      (forget C n)).RespectsIso)

/-- Reindexing along a simplex map preserves pointwise stage weak
equivalences: the component at `a₀` is the hypothesis at
`indexFunctor f a₀`, transported along the definitional
`forget`/`whiskeringLeft`/`evaluation` mapping of `reindexStage`. -/
theorem stageWeak_of_reindexStage {a b : SimplexCategory} (f : a ⟶ b)
    {X Y : Stage C b.len} (φ : X ⟶ Y) (h : stageWeak C b.len φ) :
    stageWeak C a.len ((reindexStage f).map φ) := by
  rw [mem_stageWeak] at h ⊢
  intro a₀
  exact h ((indexFunctor f).obj a₀)

end CategoryTheory.Waldhausen.SConstruction
