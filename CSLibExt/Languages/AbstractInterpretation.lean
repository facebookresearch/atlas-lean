/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.FixedPoints

/-!
# Abstract interpretation: least-fixpoint soundness

The fixpoint core of abstract interpretation, in the lattice framework
introduced by P. Cousot and R. Cousot (POPL 1977). If a monotone
abstract transformer over-approximates a monotone concrete transformer
on sets of states through a Galois connection, then the abstraction of
the concrete least fixpoint is below the abstract least fixpoint
(`abs_lfp_sound`). The one-point abstract domain `PUnit`, which
forgets all information, is the trivial instance: `top_domain_gc` is
its Galois connection and `top_domain_sound` its transfer condition.

A collecting semantics for a concrete language and widening operators
are not formalized here.
-/

@[expose] public section

namespace Cslib.AbstractInterpretation

/-- Least-fixpoint soundness of abstract interpretation. Let `α ⊣ γ`
be a Galois connection between a complete lattice structure on the
concrete state sets `Set State` and a complete lattice `A` of abstract
values, `F` a monotone concrete transformer, and `F'` a monotone
abstract transformer satisfying the pointwise transfer condition
`α (F (γ a)) ≤ F' a`. Then the abstraction of the least fixpoint of
`F` is below the least fixpoint of `F'`. -/
theorem abs_lfp_sound {State A : Type*} [CompleteLattice (Set State)]
    [CompleteLattice A] (α : Set State → A) (γ : A → Set State)
    (gc : GaloisConnection α γ)
    (F : Set State → Set State) (hF : Monotone F)
    (F' : A → A) (hF' : Monotone F')
    (hsound : ∀ a, α (F (γ a)) ≤ F' a) :
    α (OrderHom.lfp ⟨F, hF⟩) ≤ OrderHom.lfp ⟨F', hF'⟩ := by
  have hfix : F' (OrderHom.lfp ⟨F', hF'⟩) = OrderHom.lfp ⟨F', hF'⟩ :=
    OrderHom.isFixedPt_lfp ⟨F', hF'⟩
  have h := hsound (OrderHom.lfp ⟨F', hF'⟩)
  rw [hfix] at h
  have hpre := gc.le_iff_le.mp h
  have hle := OrderHom.lfp_le ⟨F, hF⟩ hpre
  exact gc.le_iff_le.mpr hle

/-- The one-point abstract domain: abstraction to the single value of
`PUnit` and concretization to the universal set form a Galois
connection. -/
theorem top_domain_gc {State : Type*} :
    GaloisConnection (fun _ : Set State => PUnit.unit)
      (fun _ : PUnit => (Set.univ : Set State)) :=
  fun _ _ => iff_of_true le_rfl (Set.subset_univ _)

/-- The transfer condition of `abs_lfp_sound` for the one-point domain:
with abstraction `fun _ => PUnit.unit`, concretization
`fun _ => Set.univ` (`top_domain_gc`), and the identity abstract
transformer, `α (F (γ a)) ≤ a` holds for every concrete transformer
`F`. -/
theorem top_domain_sound {State : Type*} (F : Set State → Set State) :
    ∀ a : PUnit, (fun _ => PUnit.unit) (F (Set.univ)) ≤ a := by
  intro a
  cases a
  exact le_refl _

end Cslib.AbstractInterpretation
