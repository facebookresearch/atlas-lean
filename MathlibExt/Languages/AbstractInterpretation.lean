/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.FixedPoints

@[expose] public section

/-- Abstract-interpretation soundness at the fixpoint level
(framework core of VER-13; the IMP collecting semantics and
widening are downstream parts of the roadmap package).

Given a Galois connection `α ⊣ γ` between concrete sets of
states and an abstract domain `A`, a monotone concrete
transformer `F`, and a monotone abstract transformer `F#` that is
pointwise sound (`α (F (γ a)) ≤ F# a`), the abstraction of the
concrete least fixpoint is below the abstract least fixpoint. -/
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

/-- The trivial (top) abstract domain is sound for every concrete
transformer: with `A = PUnit`, abstraction maps everything to the
single abstract value and concretization is the universal set. -/
theorem top_domain_sound {State : Type*} (F : Set State → Set State) :
    ∀ a : PUnit, (fun _ => PUnit.unit) (F (Set.univ)) ≤ a := by
  intro a
  cases a
  exact le_refl _
