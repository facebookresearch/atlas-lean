/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_groupCohomology_H1_subsingleton_of_isUnit_card.lean`
and
`P2M/Sol/S_groupCohomology_H1_subsingleton_of_isUnit_card.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section

universe u

open CategoryTheory

namespace groupCohomology.H1

private lemma sum_reindex_mulLeft {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A : Rep k G} (F : G → A) (g : G) :
    ∑ h : G, F (g * h) = ∑ h : G, F h :=
  Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

/-- First group cohomology vanishes when the group order is invertible.

Averaging a cocycle over the group exhibits it as a coboundary: if
`∑ h, f h = s`, the cocycle relation gives `(#G) • f g = s - ρ g s`, and
dividing by `#G` produces the cobounding element. -/
public theorem subsingleton_of_isUnit_card {k G : Type u} [CommRing k] [Group G]
    [Fintype G] (A : Rep k G) (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H1 A) := by
  have hle : groupCohomology.cocycles₁ A ≤ groupCohomology.coboundaries₁ A := by
    intro f hf
    set s : A := ∑ h : G, f h with hs
    have key : ∀ g : G, (Fintype.card G) • f g = s - A.ρ g s := by
      intro g
      have h1 : (∑ h : G, f (g * h)) = ∑ h : G, (A.ρ g (f h) + f g) :=
        Finset.sum_congr rfl fun h _ => (groupCohomology.mem_cocycles₁_iff f).1 hf g h
      rw [sum_reindex_mulLeft f g, Finset.sum_add_distrib, ← map_sum, Finset.sum_const,
        Finset.card_univ, ← hs] at h1
      rw [eq_sub_iff_add_eq, add_comm]
      exact h1.symm
    refine ⟨-((↑hG.unit⁻¹ : k) • s), funext fun g => ?_⟩
    show A.ρ g (-((↑hG.unit⁻¹ : k) • s)) - (-((↑hG.unit⁻¹ : k) • s)) = f g
    have heq : A.ρ g (-((↑hG.unit⁻¹ : k) • s)) - -((↑hG.unit⁻¹ : k) • s)
        = (↑hG.unit⁻¹ : k) • (s - A.ρ g s) := by
      simp only [map_neg, map_smul, smul_sub]
      abel
    rw [heq, ← key g, ← Nat.cast_smul_eq_nsmul k, smul_smul, hG.val_inv_mul, one_smul]
  exact subsingleton_of_forall_eq 0 fun x =>
    groupCohomology.H1_induction_on x fun y =>
      (groupCohomology.H1π_eq_zero_iff y).2 (hle y.2)

end groupCohomology.H1
