/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.SingleObj

/-!
# Extending a based homomorphism to a groupoid

For an arbitrary groupoid and a homomorphism from the original endomorphism group at a
chosen object, `Groupoid.basedFunctor` constructs a functor to `SingleObj G`. It uses
normalized connectors in the component of that object and sends every arrow in the other
components to `1`.

Both `End` multiplication and `SingleObj` composition use reversed categorical composition.
The normalization makes the induced homomorphism at the original object exactly the given
homomorphism.

This is the reusable groupoid construction in the project-authored quotient-valued groupoid
decomposition for Weibel, Exercise IV.1.4.
-/

@[expose] public section

set_option autoImplicit false

universe v u w

namespace CategoryTheory
namespace Groupoid

variable {C : Type u} [Groupoid.{v} C]
variable {G : Type w} [Group G]

/-- Choose a connector from `c₀` to a reachable object, using the identity at `c₀`. -/
noncomputable def basedFunctorConnector (c₀ c : C) (h : Nonempty (c₀ ⟶ c)) : c₀ ⟶ c := by
  classical
  exact if hc : c = c₀ then eqToHom hc.symm else Classical.choice h

/-- The chosen connector at the original base object is the identity. -/
@[simp]
theorem basedFunctorConnector_self (c₀ : C) (h : Nonempty (c₀ ⟶ c₀)) :
    basedFunctorConnector c₀ c₀ h = 𝟙 c₀ := by
  classical
  simp [basedFunctorConnector]

/-- Apply the original homomorphism to the loop formed using the normalized connectors.
Arrows outside the component of `c₀` have value `1`. -/
noncomputable def basedFunctorMap (c₀ : C) (φ : End c₀ →* G) {c d : C} (f : c ⟶ d) : G := by
  classical
  exact if hc : Nonempty (c₀ ⟶ c) then
    φ (End.of (basedFunctorConnector c₀ c hc ≫ f ≫
      Groupoid.inv (basedFunctorConnector c₀ d ⟨basedFunctorConnector c₀ c hc ≫ f⟩)))
  else 1

/-- On the original component, the arrow map evaluates the same original based loop. -/
theorem basedFunctorMap_of_nonempty (c₀ : C) (φ : End c₀ →* G) {c d : C} (f : c ⟶ d)
    (hc : Nonempty (c₀ ⟶ c)) (hd : Nonempty (c₀ ⟶ d)) :
    basedFunctorMap c₀ φ f =
      φ (End.of (basedFunctorConnector c₀ c hc ≫ f ≫
        Groupoid.inv (basedFunctorConnector c₀ d hd))) := by
  classical
  simp only [basedFunctorMap, dite_eq_left hc]

/-- The arrow map is trivial on every component without a morphism from the base object. -/
theorem basedFunctorMap_of_not_nonempty (c₀ : C) (φ : End c₀ →* G) {c d : C} (f : c ⟶ d)
    (hc : ¬ Nonempty (c₀ ⟶ c)) : basedFunctorMap c₀ φ f = 1 := by
  classical
  simp only [basedFunctorMap, dite_eq_right hc]

private theorem basedFunctor_nonempty_iff (c₀ : C) {c d : C} (f : c ⟶ d) :
    Nonempty (c₀ ⟶ c) ↔ Nonempty (c₀ ⟶ d) := by
  constructor
  · rintro ⟨a⟩
    exact ⟨a ≫ f⟩
  · rintro ⟨a⟩
    exact ⟨a ≫ Groupoid.inv f⟩

private theorem basedFunctorMap_id (c₀ : C) (φ : End c₀ →* G) (c : C) :
    basedFunctorMap c₀ φ (𝟙 c) = 1 := by
  classical
  by_cases hc : Nonempty (c₀ ⟶ c)
  · rw [basedFunctorMap_of_nonempty c₀ φ (𝟙 c) hc hc]
    have hLoop :
        (End.of (basedFunctorConnector c₀ c hc ≫ 𝟙 c ≫
          Groupoid.inv (basedFunctorConnector c₀ c hc)) : End c₀) = 1 := by
      apply End.ext
      change basedFunctorConnector c₀ c hc ≫ 𝟙 c ≫
        Groupoid.inv (basedFunctorConnector c₀ c hc) = 𝟙 c₀
      simp only [Category.id_comp, Groupoid.inv_eq_inv, IsIso.hom_inv_id]
    rw [hLoop, map_one]
  · exact basedFunctorMap_of_not_nonempty c₀ φ (𝟙 c) hc

private theorem basedFunctorMap_comp (c₀ : C) (φ : End c₀ →* G) {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) :
    basedFunctorMap c₀ φ (f ≫ g) = basedFunctorMap c₀ φ g * basedFunctorMap c₀ φ f := by
  classical
  by_cases hc : Nonempty (c₀ ⟶ c)
  · have hd : Nonempty (c₀ ⟶ d) := (basedFunctor_nonempty_iff c₀ f).mp hc
    have he : Nonempty (c₀ ⟶ e) := (basedFunctor_nonempty_iff c₀ g).mp hd
    rw [basedFunctorMap_of_nonempty c₀ φ (f ≫ g) hc he,
      basedFunctorMap_of_nonempty c₀ φ g hd he,
      basedFunctorMap_of_nonempty c₀ φ f hc hd]
    have hLoop :
        (End.of (basedFunctorConnector c₀ c hc ≫ (f ≫ g) ≫
          Groupoid.inv (basedFunctorConnector c₀ e he)) : End c₀) =
        End.of (basedFunctorConnector c₀ d hd ≫ g ≫
          Groupoid.inv (basedFunctorConnector c₀ e he)) *
        End.of (basedFunctorConnector c₀ c hc ≫ f ≫
          Groupoid.inv (basedFunctorConnector c₀ d hd)) := by
      apply End.ext
      change basedFunctorConnector c₀ c hc ≫ (f ≫ g) ≫
        Groupoid.inv (basedFunctorConnector c₀ e he) =
        (basedFunctorConnector c₀ c hc ≫ f ≫
          Groupoid.inv (basedFunctorConnector c₀ d hd)) ≫
        (basedFunctorConnector c₀ d hd ≫ g ≫
          Groupoid.inv (basedFunctorConnector c₀ e he))
      simp only [Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    exact (congrArg φ hLoop).trans (φ.map_mul _ _)
  · have hd : ¬ Nonempty (c₀ ⟶ d) := by
      intro h
      exact hc ((basedFunctor_nonempty_iff c₀ f).mpr h)
    rw [basedFunctorMap_of_not_nonempty c₀ φ (f ≫ g) hc,
      basedFunctorMap_of_not_nonempty c₀ φ g hd,
      basedFunctorMap_of_not_nonempty c₀ φ f hc, one_mul]

/-- Extend an original based homomorphism to the whole groupoid, trivially on other components. -/
noncomputable def basedFunctor (c₀ : C) (φ : End c₀ →* G) : C ⥤ SingleObj G where
  obj _ := SingleObj.star G
  map f := basedFunctorMap c₀ φ f
  map_id c := by
    change basedFunctorMap c₀ φ (𝟙 c) = 1
    exact basedFunctorMap_id c₀ φ c
  map_comp f g := by
    change basedFunctorMap c₀ φ (f ≫ g) = basedFunctorMap c₀ φ g * basedFunctorMap c₀ φ f
    exact basedFunctorMap_comp c₀ φ f g

/-- The extension has the unique original object of `SingleObj G` as its object value. -/
theorem basedFunctor_obj (c₀ : C) (φ : End c₀ →* G) (c : C) :
    (basedFunctor c₀ φ).obj c = SingleObj.star G := rfl

/-- The extension sends a reachable arrow to the original conjugated based loop under `φ`. -/
theorem basedFunctor_map_of_nonempty (c₀ : C) (φ : End c₀ →* G) {c d : C} (f : c ⟶ d)
    (hc : Nonempty (c₀ ⟶ c)) (hd : Nonempty (c₀ ⟶ d)) :
    (basedFunctor c₀ φ).map f =
      φ (End.of (basedFunctorConnector c₀ c hc ≫ f ≫
        Groupoid.inv (basedFunctorConnector c₀ d hd))) := by
  exact basedFunctorMap_of_nonempty c₀ φ f hc hd

/-- The extension is trivial on all arrows in the other components. -/
theorem basedFunctor_map_of_not_nonempty (c₀ : C) (φ : End c₀ →* G) {c d : C} (f : c ⟶ d)
    (hc : ¬ Nonempty (c₀ ⟶ c)) : (basedFunctor c₀ φ).map f = 1 := by
  exact basedFunctorMap_of_not_nonempty c₀ φ f hc

/-- On each original based endomorphism, the extension agrees exactly with `φ`. -/
@[simp]
theorem basedFunctor_map_end (c₀ : C) (φ : End c₀ →* G) (e : End c₀) :
    (basedFunctor c₀ φ).map e.asHom = φ e := by
  rw [basedFunctor_map_of_nonempty c₀ φ e.asHom ⟨𝟙 c₀⟩ ⟨𝟙 c₀⟩]
  simp only [basedFunctorConnector_self, Groupoid.inv_eq_inv, IsIso.inv_id,
    Category.id_comp, Category.comp_id]

/-- Every normalized connector has trivial image under the extension. -/
theorem basedFunctor_map_connector (c₀ : C) (φ : End c₀ →* G) (c : C)
    (hc : Nonempty (c₀ ⟶ c)) :
    (basedFunctor c₀ φ).map (basedFunctorConnector c₀ c hc) = 1 := by
  rw [basedFunctor_map_of_nonempty c₀ φ (basedFunctorConnector c₀ c hc) ⟨𝟙 c₀⟩ hc,
    basedFunctorConnector_self, Category.id_comp]
  have hLoop :
      (End.of (basedFunctorConnector c₀ c hc ≫
        Groupoid.inv (basedFunctorConnector c₀ c hc)) : End c₀) = 1 := by
    apply End.ext
    change basedFunctorConnector c₀ c hc ≫
      Groupoid.inv (basedFunctorConnector c₀ c hc) = 𝟙 c₀
    simp only [Groupoid.inv_eq_inv, IsIso.hom_inv_id]
  rw [hLoop, map_one]

/-- The original based homomorphism recovered using the stock `SingleObj.toEnd` is `φ`. -/
theorem basedFunctor_mapEnd (c₀ : C) (φ : End c₀ →* G) :
    (SingleObj.toEnd G).symm.toMonoidHom.comp ((basedFunctor c₀ φ).mapEnd c₀) = φ := by
  apply MonoidHom.ext
  intro e
  change (basedFunctor c₀ φ).map e.asHom = φ e
  exact basedFunctor_map_end c₀ φ e

end Groupoid
end CategoryTheory
