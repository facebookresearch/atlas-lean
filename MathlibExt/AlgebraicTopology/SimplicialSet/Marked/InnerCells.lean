/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Native minimally marked inner-horn cells

The minimal-marking/forgetful adjunction transports the original whole
lifting problem. The right lifting condition for the minimally marked
inner horns is exactly the actual inner-fibration condition of the original
underlying map. No marked-model structure is assumed.
-/

universe u
open CategoryTheory
open scoped Simplicial

namespace SSet.Marked

/-- The original inner horn inclusion with its actual minimal source and target markings. -/
def innerCell (n : ℕ) (i : Fin (n + 3)) :
    min (Λ[n + 2, i] : SSet.{u}) ⟶ min (Δ[n + 2] : SSet.{u}) :=
  minimal.map (horn.{u} (n + 2) i).ι

/-- The marked cell retains the original complete inner horn inclusion. -/
@[simp]
theorem innerCell_hom (n : ℕ) (i : Fin (n + 3)) :
    (innerCell.{u} n i).hom = (horn.{u} (n + 2) i).ι := rfl

/-- The actual marked inner-horn cell is monic on its original carrier. -/
theorem innerCell_mono (n : ℕ) (i : Fin (n + 3)) : Mono (innerCell.{u} n i) := by
  let _ : Mono (innerCell.{u} n i).hom := inferInstanceAs (Mono (horn.{u} (n + 2) i).ι)
  exact Hom.mono_of_underlying _

/-- The existing marking adjunction transports the whole original lifting problem exactly. -/
theorem minimal_hasLiftingProperty_iff {A D : SSet.{u}} (i : A ⟶ D) {X Y : Marked.{u}}
    (p : X ⟶ Y) : HasLiftingProperty (minimal.map i) p ↔ HasLiftingProperty i p.hom :=
  minimalAdjunction.hasLiftingProperty_iff i p

/-- Lifting the actual marked inner cells is precisely the native inner-fibration condition. -/
theorem innerCell_rlp_iff {X Y : Marked.{u}} (p : X ⟶ Y) :
    (∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
      HasLiftingProperty (innerCell.{u} n i) p) ↔ InnerFibration p.hom := by
  constructor
  · intro hp
    refine ⟨fun A D i hi => ?_⟩
    obtain ⟨j, hj, hk⟩ := hi
    exact (minimal_hasLiftingProperty_iff _ p).mp (hp _ j hj hk)
  · intro hp n i hi hk
    let _ : InnerFibration p.hom := hp
    apply (minimal_hasLiftingProperty_iff _ p).mpr
    exact InnerFibration.mem _ (innerHornInclusions.intro i hi hk)

end SSet.Marked
