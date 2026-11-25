/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Original products and limiting fans of fibrant weak maps

The complete generic declarations are retained from the original native
Omega weak-class source. Original universes, chosen fans/cofans, maps,
hypotheses and proof bodies are unchanged.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w uC vC uD vD uV vV uI uT
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {J : Type w} [HasProductsOfShape J C]

/-- Products of genuine trivial fibrations satisfy the original trivial fibration class. -/
theorem originalPiMap_trivialFibration {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, trivialFibrations C (f j)) : trivialFibrations C (Limits.Pi.map f) := by
  rw [← cofibrations_rlp] at hf ⊢
  exact MorphismProperty.IsStableUnderLimitsOfShape.condition
    (Discrete.functor X) (Discrete.functor Y)
    (Fan.mk (∏ᶜ X) (Pi.π X)) (Fan.mk (∏ᶜ Y) (Pi.π Y)) (productIsProduct X) (productIsProduct Y)
    (Discrete.natTrans (fun j => f j.as)) (fun j => hf j.as) (Limits.Pi.map f)
    (fun j => Pi.map_π f j.as)

/-- The original Brown factorizations prove weakness of every product of fibrant weak arrows. -/
theorem originalPiMap_weakEquivalence_of_fibrant {X Y : J → C}
    (f : ∀ j, X j ⟶ Y j) [∀ j, IsFibrant (X j)] [∀ j, IsFibrant (Y j)]
    (hf : ∀ j, WeakEquivalence (f j)) : WeakEquivalence (Limits.Pi.map f) := by
  classical
  let h : ∀ j, FibrantBrownFactorization (f j) :=
    fun j => Classical.choice inferInstance
  let Z : J → C := fun j => (h j).Z
  let i : ∀ j, X j ⟶ Z j := fun j => (h j).i
  let p : ∀ j, Z j ⟶ Y j := fun j => (h j).p
  let r : ∀ j, Z j ⟶ X j := fun j => (h j).r
  have hp : ∀ j, trivialFibrations C (p j) := by
    intro j
    let _ : WeakEquivalence (f j) := hf j
    exact mem_trivialFibrations (p j)
  have hr : ∀ j, trivialFibrations C (r j) := fun j => mem_trivialFibrations (r j)
  let _ : WeakEquivalence (Limits.Pi.map p) :=
    (mem_trivialFibrations_iff _).mp (originalPiMap_trivialFibration p hp) |>.2
  let _ : WeakEquivalence (Limits.Pi.map r) :=
    (mem_trivialFibrations_iff _).mp (originalPiMap_trivialFibration r hr) |>.2
  have hRetract : Limits.Pi.map i ≫ Limits.Pi.map r = 𝟙 (∏ᶜ X) := by
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, Pi.map_π, ← Category.assoc, Pi.map_π,
      Category.assoc, (h j).i_r, Category.comp_id, Category.id_comp]
  let _ : WeakEquivalence (Limits.Pi.map i) := weakEquivalence_of_postcomp_of_fac hRetract
  have hFac : Limits.Pi.map i ≫ Limits.Pi.map p = Limits.Pi.map f := by
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, Pi.map_π, ← Category.assoc, Pi.map_π, Category.assoc, (h j).fac]
    exact (Pi.map_π f j).symm
  rw [← hFac]
  infer_instance

end HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {J : Type w} [HasProductsOfShape J C]

/-- An actual map between two original limiting fans is weak whenever its
complete fibrant component maps are weak and all actual projection squares commute. -/
theorem originalFanMap_weak_of_fibrant
    {X Y : J → C} [∀ j, IsFibrant (X j)] [∀ j, IsFibrant (Y j)]
    (c : Fan X) (hc : IsLimit c) (d : Fan Y) (hd : IsLimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, p ≫ d.proj j = c.proj j ≫ f j)
    (hf : ∀ j, WeakEquivalence (f j)) : WeakEquivalence p := by
  let ex := hc.conePointUniqueUpToIso (productIsProduct X)
  let ey := hd.conePointUniqueUpToIso (productIsProduct Y)
  have hx (j : J) : ex.hom ≫ Pi.π X j = c.proj j :=
    IsLimit.conePointUniqueUpToIso_hom_comp hc (productIsProduct X) (Discrete.mk j)
  have hy (j : J) : ey.hom ≫ Pi.π Y j = d.proj j :=
    IsLimit.conePointUniqueUpToIso_hom_comp hd (productIsProduct Y) (Discrete.mk j)
  have h : p ≫ ey.hom = ex.hom ≫ Limits.Pi.map f := by
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, hy, hp, Category.assoc, Pi.map_π, ← Category.assoc, hx]
  let _ : WeakEquivalence (Limits.Pi.map f) := originalPiMap_weakEquivalence_of_fibrant f hf
  let _ : WeakEquivalence (p ≫ ey.hom) := h.symm ▸ inferInstanceAs (WeakEquivalence (ex.hom ≫
    Limits.Pi.map f))
  exact weakEquivalence_of_postcomp p ey.hom

end HomotopicalAlgebra
