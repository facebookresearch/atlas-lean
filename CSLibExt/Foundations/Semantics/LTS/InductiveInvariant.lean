/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.Basic

/-! # Safety by inductive invariants -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTS

variable {State Label : Type*} (lts : LTS State Label)

/-- The states reachable by a finite trace, including the empty trace, from an initial set. -/
def reachableFrom (initial : Set State) : Set State :=
  {t | ∃ s ∈ initial, lts.CanReach s t}

/-- A set is inductive from `initial` if it contains all initial states and is preserved by
one step with any label. -/
def InductiveFrom (initial J : Set State) : Prop :=
  initial ⊆ J ∧ lts.TrInv (· ∈ J)

/-- The set of reachable states contains the initial set and is closed under steps. -/
theorem reachableFrom_inductive (initial : Set State) :
    lts.InductiveFrom initial (lts.reachableFrom initial) := by
  refine ⟨fun s hs => ⟨s, hs, CanReach.refl lts s⟩, ?_⟩
  intro s a t hst hs
  obtain ⟨s₀, hinit, hreach⟩ := hs
  exact ⟨s₀, hinit, hreach.trans ⟨[a], MTr.single lts hst⟩⟩

/-- Every inductive set contains every state reachable from its initial set. -/
theorem reachableFrom_subset_of_inductive {initial J : Set State}
    (hJ : lts.InductiveFrom initial J) : lts.reachableFrom initial ⊆ J := by
  rintro t ⟨s, hs, labels, hst⟩
  exact mtrInv_of_trInv hJ.2 s labels t hst (hJ.1 hs)

/-- Reachability from an initial set is the least inductive set under inclusion. -/
theorem isLeast_reachableFrom (initial : Set State) :
    IsLeast {J | lts.InductiveFrom initial J} (lts.reachableFrom initial) :=
  ⟨lts.reachableFrom_inductive initial, fun _ hJ => lts.reachableFrom_subset_of_inductive hJ⟩

/-- **Safety by inductive invariants.** No bad state is reachable from the initial set exactly
when an inductive set is disjoint from the bad states. The reachable set witnesses existence
in the forward direction. Neither the state space nor the label type needs to be finite.

Source: A. R. Bradley, *SAT-Based Model Checking without Unrolling*, VMCAI 2011, §§2–3. -/
theorem disjoint_reachableFrom_iff_exists_inductive (initial bad : Set State) :
    Disjoint (lts.reachableFrom initial) bad ↔
      ∃ J, lts.InductiveFrom initial J ∧ Disjoint J bad := by
  constructor
  · intro hsafe
    exact ⟨_, lts.reachableFrom_inductive initial, hsafe⟩
  · rintro ⟨J, hJ, hsafe⟩
    exact hsafe.mono_left (lts.reachableFrom_subset_of_inductive hJ)

end Cslib.LTS
