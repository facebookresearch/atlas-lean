/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.CongTyping
import CSLibExt.Languages.SessionTypes.Endpoint.RankedCong

/-!
# Reverse scope when the lifted partner initially owns both completed bound roles
-/

namespace Cslib.SessionTypes.Endpoint.ReverseScopeCompletedTests

open PiCalculus

def completed : Capability := ⟨11, .done⟩
def partner : Proc := .par .nil .nil

/-- Both completed bound roles are allocated to the partner, not the left nil. -/
theorem partner_owns_bound_pair :
    HasType 1 (Context.bind completed ∅) (liftProc 0 partner) := by
  rw [Context.bind_empty]
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · exact HasType.nil_singleton (by change 0 < 1; decide)
  · exact HasType.nil_singleton (by change 0 < 1; decide)

/-- The restricted source has an actual split: empty ownership on left,
completed bound pair entirely on the lifted right partner. -/
theorem restricted_source_typed :
    HasType 0 ∅ (.nu (.par .nil (liftProc 0 partner))) := by
  apply HasType.nu (c := completed)
  have hnil : HasType 1 ∅ .nil := by
    apply HasType.nil
    · intro e c he
      simp at he
    · intro e he
      exact False.elim (Finmap.notMem_empty he)
  have ht := HasType.par (Finmap.disjoint_empty (Context.bind completed ∅))
    hnil partner_owns_bound_pair
  simpa only [Finmap.empty_union] using ht

/-- Reverse scope derives completion, erases the partner's fresh slots,
and reattaches that pair to the restricted nil with unchanged empty interface. -/
theorem reverse_reallocates_completed_bound_slots :
    HasType 0 ∅ (.par (.nu .nil) partner) :=
  restricted_source_typed.scope_reverse

/-- Mixed allocation: one completed role belongs to the restricted body,
and its peer belongs to the lifted partner. This pins both restoration branches. -/
theorem mixed_role_source_typed : HasType 0 ∅ (.nu (.par .nil (liftProc 0 .nil))) := by
  apply HasType.nu (c := completed)
  rw [Context.bind_empty]
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · exact HasType.nil_singleton (Nat.zero_lt_succ 0)
  · exact HasType.nil_singleton (Nat.zero_lt_succ 0)

/-- Generic Cong transport, not a special closed-hole theorem, reverses the
mixed allocation using exactly its original typing derivation. -/
theorem mixed_role_reverse_scope : HasType 0 ∅ (.par (.nu .nil) .nil) :=
  (HasType.cong_iff (Cong.symm (Cong.scope .nil .nil))).mp mixed_role_source_typed

/-- Both completed partner-owned roles are admitted by the SAME refinement. -/
theorem partner_pair_ranked :
    RankedType 1 (Context.bind completed ∅) (liftProc 0 partner) := by
  rw [Context.bind_empty]
  apply RankedType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))
  · exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))

/-- The general ranked Cong theorem restores both absent completed roles
from the partner without adding an active guard dependency. -/
theorem partner_pair_ranked_reverse : RankedType 0 ∅ (.par (.nu .nil) partner) := by
  have hn : RankedType 1 ∅ .nil := RankedType.nil
    (by intro e c he; simp at he) (by intro e he; exact False.elim (Finmap.notMem_empty he))
  have ht := RankedType.par (Finmap.disjoint_empty (Context.bind completed ∅)) hn partner_pair_ranked
  rw [Finmap.empty_union] at ht
  exact (RankedType.cong_iff (Cong.symm (Cong.scope .nil partner))).mp (RankedType.nu ht)

/-- One completed role on each side exercises mixed restoration in ranked scope. -/
theorem mixed_role_ranked_source : RankedType 0 ∅ (.nu (.par .nil (liftProc 0 .nil))) := by
  apply RankedType.nu (c := completed)
  rw [Context.bind_empty]
  apply RankedType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))
  · exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))

/-- GENERAL ranked congruence transport handles mixed completed-role allocation. -/
theorem mixed_role_ranked_reverse : RankedType 0 ∅ (.par (.nu .nil) .nil) :=
  (RankedType.cong_iff (Cong.symm (Cong.scope .nil .nil))).mp mixed_role_ranked_source

end Cslib.SessionTypes.Endpoint.ReverseScopeCompletedTests
