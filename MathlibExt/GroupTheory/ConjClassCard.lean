/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer.lean`
and the corresponding `P2M/Sol/S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer.lean`
proof file in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the proof is adapted here with that machinery removed, the statement
is restated as an identity of cardinals (the source's `Nat.card` form follows
from it), and the name is restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Defs

/-!
# Conjugacy class times centralizer

The conjugacy class of an element `σ` of a group `G` is its orbit under conjugation, and its
centralizer is the stabilizer of that action, so the orbit-stabilizer bijection gives
`#{τ | IsConj σ τ} * #(centralizer {σ}) = #G` as an identity of cardinals, for every group,
finite or not.

For finite groups, the same count follows from Mathlib's
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` for the conjugation action and
`Subgroup.nat_card_centralizer_nat_card_stabilizer`.
-/

@[expose] public section

namespace ConjClassCard

variable {G : Type*} [Group G]

private theorem setOf_isConj_eq_orbit_conjAct (σ : G) :
    {τ : G | IsConj σ τ} = MulAction.orbit (ConjAct G) σ := by
  ext τ
  rw [ConjAct.orbit_eq_carrier_conjClasses, Set.mem_ofPred_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨IsConj.symm, IsConj.symm⟩

private theorem mk_stabilizer_conjAct_eq_mk_centralizer (σ : G) :
    Cardinal.mk (MulAction.stabilizer (ConjAct G) σ) =
      Cardinal.mk (Subgroup.centralizer ({σ} : Set G)) := by
  refine Cardinal.mk_congr (Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv fun g => ?_)
  change g ∈ MulAction.stabilizer (ConjAct G) σ ↔
    ConjAct.ofConjAct g ∈ Subgroup.centralizer ({σ} : Set G)
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff, ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]
  exact Iff.rfl

/-- **Class size times centralizer order, for every group.** For an element `σ` of a group `G`,
the cardinal of the conjugacy class `{τ | IsConj σ τ}` times the cardinal of the centralizer of
`σ` is the cardinal of `G`. For a finite group this is the orbit-stabilizer count
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` for the conjugation action. -/
theorem mk_setOf_isConj_mul_mk_centralizer (σ : G) :
    Cardinal.mk {τ : G | IsConj σ τ} * Cardinal.mk (Subgroup.centralizer ({σ} : Set G)) =
      Cardinal.mk G := by
  rw [setOf_isConj_eq_orbit_conjAct, ← mk_stabilizer_conjAct_eq_mk_centralizer,
    Cardinal.mk_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) σ), Cardinal.mul_def,
    ← Cardinal.mk_congr Subgroup.groupEquivQuotientProdSubgroup]
  rfl

end ConjClassCard

end
