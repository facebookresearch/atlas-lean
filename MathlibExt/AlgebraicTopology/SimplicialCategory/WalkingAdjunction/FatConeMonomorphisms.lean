/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeComponents
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The actual fat cone preserves monomorphisms

The derived component normal forms transport by the identical
original coefficient map and keep the whole nonfinal time and apex.
Consequently an original monomorphism remains injective in every
fat-cone component. The native component isomorphisms and functor
category monomorphism criterion prove monicity of the entire actual
pushout map, without a weak-map or model-category assumption.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The entire original component transport keeps its nonfinal time and fixed apex simplex. -/
def componentMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) : Component X n ⟶ Component Y n :=
  ↾(Sum.map (Prod.map (f.app (op ⦋n⦌)) id) id)

/-- Original cylinder classification commutes with the whole original coefficient map. -/
theorem classifyCylinder_map {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : (X ⊗ (Δ[1] : SSet.{u})) _⦋n⦌) :
    classifyCylinder Y n ((f ▷ (Δ[1] : SSet.{u})).app _ a) = componentMap f n (classifyCylinder X n a) := by
  rcases a with ⟨x, t⟩
  change classifyCylinder Y n (f.app _ x, t) = componentMap f n (classifyCylinder X n (x, t))
  unfold classifyCylinder
  by_cases ht : t = SSet.stdSimplex.const 1 1 _
  · rw [dite_eq_left ht, dite_eq_left ht]
    have h := NatTrans.congr_app (SSet.stdSimplex.isTerminalObj₀.hom_ext
      (f ≫ SSet.stdSimplex.isTerminalObj₀.from Y) (SSet.stdSimplex.isTerminalObj₀.from X)) (op ⦋n⦌)
    exact congrArg Sum.inr (ConcreteCategory.congr_hom h x)
  · rw [dite_eq_right ht, dite_eq_right ht]
    rfl

/-- The actual component isomorphisms commute with the full original fat-cone map. -/
theorem map_componentIso {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (map f).app (op ⦋n⦌) ≫ (componentIso Y n).hom = (componentIso X n).hom ≫ componentMap f n := by
  apply (componentPushout X n).hom_ext
  · have hc : (cylinder X).app (op ⦋n⦌) ≫ (map f).app (op ⦋n⦌) =
        (f ▷ (Δ[1] : SSet.{u})).app (op ⦋n⦌) ≫ (cylinder Y).app (op ⦋n⦌) :=
      NatTrans.congr_app (cylinder_map f) (op ⦋n⦌)
    rw [← Category.assoc, hc, Category.assoc, cylinder_componentIso,
      ← Category.assoc, cylinder_componentIso]
    apply ConcreteCategory.hom_ext
    intro a
    exact classifyCylinder_map f n a
  · have ha : (apex X).app (op ⦋n⦌) ≫ (map f).app (op ⦋n⦌) = (apex Y).app (op ⦋n⦌) :=
      NatTrans.congr_app (apex_map f) (op ⦋n⦌)
    rw [← Category.assoc, ha, apex_componentIso, ← Category.assoc, apex_componentIso]
    apply ConcreteCategory.hom_ext
    intro z
    rfl

/-- The original coefficient injectivity is retained by complete component transport. -/
theorem componentMap_injective {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (hf : Function.Injective (f.app (op ⦋n⦌))) : Function.Injective (componentMap f n) :=
  hf.prodMap Function.injective_id |>.sumMap Function.injective_id

/-- The entire actual fat-cone map of an original monomorphism is monic. -/
instance map_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] : Mono (map f) := by
  let _ : ∀ i, Mono ((map f).app i) := by
    intro i
    rcases i with ⟨⟨n⟩⟩
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro a b hab
    have ha := ConcreteCategory.congr_hom (map_componentIso f n) a
    have hb := ConcreteCategory.congr_hom (map_componentIso f n) b
    have he := congrArg (fun x => (componentIso Y n).hom x) hab
    have hn := componentMap_injective f n (CategoryTheory.injective_of_mono _) (ha.symm.trans (he.trans hb))
    exact CategoryTheory.injective_of_mono (componentIso X n).hom hn
  exact NatTrans.mono_of_mono_app _

end SSet.WalkingAdjunction.FatCone
