/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingReflection
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerCells
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# The native right class of all marked monomorphisms

A marked map lifts all actual marked monomorphisms exactly when its
original simplicial map lifts all original simplicial monomorphisms and
it reflects the actual mark set. The marked diagonal is the same full
underlying diagonal. This gives the genuine right class without a marked
weak-equivalence or model assumption.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The native marked mono right class is the original unmarked mono right class plus literal marking reflection. -/
theorem monomorphisms_rlp_iff {X Y : Marked.{u}} (p : X ⟶ Y) :
    (monomorphisms Marked.{u}).rlp p ↔ (monomorphisms SSet.{u}).rlp p.hom ∧
      ∀ e : X.toSSet _⦋1⦌, p.hom.app (op ⦋1⦌) e ∈ Y.marking → e ∈ X.marking := by
  constructor
  · intro hp
    refine ⟨?_, (edgeMarkCell_rlp_iff p).mp (hp _ edgeMarkCell_mono)⟩
    intro A D i hi
    let _ : Mono i := hi
    let _ : Mono (minimal.map i).hom := inferInstanceAs (Mono i)
    have hm : Mono (minimal.map i) := Hom.mono_of_underlying _
    exact (minimal_hasLiftingProperty_iff i p).mp (hp _ hm)
  · rintro ⟨hp, hr⟩ A D i hi
    let _ : Mono i := hi
    let _ : Mono i.hom := i.mono_underlying
    let _ : HasLiftingProperty i.hom p.hom := hp _ inferInstance
    refine ⟨fun {a b} sq => ?_⟩
    have sq' : CommSq a.hom i.hom p.hom b.hom := ⟨congrArg Hom.hom sq.w⟩
    let f : D ⟶ X := ⟨sq'.lift, fun {e} he => hr _ (by
      have h : p.hom.app (op ⦋1⦌) (sq'.lift.app (op ⦋1⦌) e) =
          b.hom.app (op ⦋1⦌) e :=
        ConcreteCategory.congr_hom (congr_app sq'.fac_right (op ⦋1⦌)) e
      exact h.symm ▸ b.preserve he)⟩
    exact CommSq.HasLift.mk' ⟨f, Hom.ext sq'.fac_left, Hom.ext sq'.fac_right⟩

end SSet.Marked
