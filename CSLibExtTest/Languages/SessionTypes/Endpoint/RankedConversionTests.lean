/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionGlobal
import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant

/-!
# Guard-checked genuine conversion-only global-progress consumers

The fresh three-state graph fixture has carrier5/payload11 and an ACTUALLY
completed receiver graph tail. Every static pre-action guard is proved below;
unranked admission alone does not establish these inequalities.
-/

namespace Cslib.SessionTypes.Endpoint.RankedConversionTests

open PiCalculus

def graph : Graph := ⟨3, fun i => if i.val = 1 then .sendName ⟨0, by decide⟩
  else if i.val = 2 then .recvName ⟨0, by decide⟩ else .done⟩
def B : Protocol := .regular graph ⟨1, by decide⟩ false
def D : Protocol := .regular graph ⟨0, by decide⟩ false
def C : Protocol := .sendName D
def A : Protocol := .sendName .done
def e : Key := ⟨.var 0, .positive⟩
def f (r : Role) : Key := ⟨.var 1, r⟩
def v : Capability := ⟨11, B⟩
def c (r : Role) : Capability := ⟨5, .sendEndpoint r 11 A .done⟩
def d (r : Role) : Capability := ⟨5, .recvEndpoint r 11 C D⟩
def Γ (r : Role) : Context := Finmap.singleton e (c r) ∪ Finmap.singleton (f r) v
def Θ (r : Role) : Context := Finmap.singleton e.opposite (d r)
def Ψ (r : Role) : Context := Finmap.singleton (f r).opposite v.dual
def Ω (r : Role) : Context := Γ r ∪ (Θ r ∪ Ψ r)
def snd : Proc := .out e.name (.var 1) .nil
def rcv : Proc := .inp e.name (.out (.var 0) (.const 401) .nil)
def peer : Proc := .inp (.var 1) .nil
def p : Proc := .par snd (.par rcv peer)
def p₁ : Proc := .par .nil (.par (.out (.var 1) (.const 401) .nil) peer)
def p₂ : Proc := .par .nil (.par .nil .nil)

theorem D_done : D.unfold = .done := rfl
theorem D_equiv : D.TreeEquiv .done := Protocol.treeEquiv_iff_head.mpr HeadMatch.done
theorem C_A_equiv : C.TreeEquiv A := D_equiv.sendName
theorem B_A_equiv : B.TreeEquiv A := B.treeEquiv_unfold.trans C_A_equiv

/-- The active owned payload participates before transfer, not after erasure. -/
theorem sender_guard (r : Role) : GuardMin (Γ r) e 5 := by
  intro x w hx ha hne
  rcases Finmap.mem_union.mp (Finmap.mem_of_lookup_eq_some hx) with hx' | hx'
  · exact False.elim (hne ((Finmap.mem_singleton _ _ _).mp hx'))
  · have he := (Finmap.mem_singleton _ _ _).mp hx'
    subst x
    rw [Γ, Finmap.lookup_union_right (by simp [e, f, Finmap.mem_singleton]),
      Finmap.lookup_singleton_eq] at hx
    cases hx
    exact (by decide : 5 < 11)

private theorem erase_singleton (x : Key) (w : Capability) :
    (Finmap.singleton x w : Context).erase x = ∅ := by
  apply Finmap.ext_lookup
  intro y
  by_cases he : y = x
  · subst y
    rw [Finmap.lookup_erase, Finmap.lookup_empty]
  · rw [Finmap.lookup_erase_ne he, Finmap.lookup_eq_none.mpr (by simpa using he),
      Finmap.lookup_empty]

/-- Exact sender residual has only its advanced completed carrier. -/
theorem sender_residual (r : Role) : Conversion.RankedType 2
    (((Γ r).erase (f r)).insert e ⟨5, .done⟩) .nil := by
  rw [Γ, Context.erase_union, Context.erase_of_notMem (by simp [e, f, Finmap.mem_singleton]),
    erase_singleton, Finmap.union_empty, Finmap.insert_singleton_eq]
  exact Conversion.RankedType.nil_of_hasType (Conversion.HasType.of_raw
    (Endpoint.HasType.nil_singleton_completed (by change 0 < 2; decide) rfl))

/-- Endpoint output checks the actual pre-transfer B/rank11 slot. -/
theorem sender_ranked (r : Role) : Conversion.RankedType 2 (Γ r) snd := by
  apply Conversion.RankedType.outEndpoint (e := e) (d := f r) (c := c r) (v := v)
    (k := 11) (t := A) (s := .done) (sender_guard r)
  · exact (Finmap.lookup_union_left (by simp)).trans Finmap.lookup_singleton_eq
  · rfl
  · exact (Finmap.lookup_union_right (by simp [e, f, Finmap.mem_singleton])).trans
      Finmap.lookup_singleton_eq
  · exact ⟨rfl, B_A_equiv⟩
  · simp [e, f]
  · change 0 < 2
    decide
  · change 1 < 2
    decide
  · exact sender_residual r

/-- Only the received slot is active; the actual carrier graph tail is done. -/
theorem receiver_ranked (r : Role) : Conversion.RankedType 2 (Θ r) rcv := by
  apply Conversion.RankedType.inpEndpoint (e := e.opposite) (c := d r) (r := r)
    (k := 11) (t := C) (s := D) (guardMin_singleton _ _)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Nat.zero_lt_succ 1
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    apply Conversion.RankedType.outName (e := ⟨.var 0, r⟩) (c := ⟨11, C⟩) (s := D)
    · intro x w hx ha hne
      rw [Finmap.lookup_insert_of_ne _ hne] at hx
      have hk := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hx)
      subst x
      rw [Finmap.lookup_singleton_eq] at hx
      cases hx
      exact False.elim (ha D_done)
    · exact Finmap.lookup_insert _
    · rfl
    · exact Nat.zero_lt_succ 2
    · trivial
    · rw [Finmap.insert_insert]
      have ht : Conversion.RankedType 3
          (Finmap.singleton (⟨.var 1, .negative⟩ : Key) (⟨5, D⟩ : Capability)) .nil :=
        Conversion.RankedType.nil_of_hasType (Conversion.HasType.of_raw
          (Endpoint.HasType.nil_singleton_completed (by change 1 < 3; decide) D_done))
      exact ht.weaken_completed (by simp [Finmap.mem_singleton]) D_done (Nat.zero_lt_succ 2)

/-- The third thread guards only its own payload peer. -/
theorem peer_ranked (r : Role) : Conversion.RankedType 2 (Ψ r) peer := by
  apply Conversion.RankedType.inpName (e := (f r).opposite) (c := v.dual) (s := D.dual)
    (guardMin_singleton _ _)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · change 1 < 2
    decide
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact Conversion.RankedType.nil_of_hasType (Conversion.HasType.of_raw
      (Endpoint.HasType.nil_singleton_completed (by change 2 < 3; decide) rfl))

/-- Genuine disjoint three-thread source; no ready/normal-form premise. -/
theorem network_ranked (r : Role) : Conversion.RankedType 2 (Ω r) p := by
  have h₁ : Finmap.Disjoint (Γ r) (Θ r ∪ Ψ r) := by
    cases r <;> simp [Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite, Finmap.Disjoint,
      Finmap.mem_singleton]
  have h₂ : Finmap.Disjoint (Θ r) (Ψ r) := by
    simp [Θ, Ψ, e, f, Key.opposite, Finmap.Disjoint, Finmap.mem_singleton]
  exact Conversion.RankedType.par h₁ (sender_ranked r)
    (Conversion.RankedType.par h₂ (receiver_ranked r) (peer_ranked r))

def privatePayload (r : Role) : Capability := match r with | .positive => v | .negative => v.dual
def K (r : Role) : Context := Context.bind (c r) (Context.bind (privatePayload r) ∅)

private theorem lookup_singleton_ne (x y : Key) (w : Capability) (h : y ≠ x) :
    (Finmap.singleton x w : Context).lookup y = none :=
  Finmap.lookup_eq_none.mpr (by simpa using h)

attribute [local simp] lookup_singleton_ne Finmap.lookup_singleton_eq

/-- Equivalent chosen private codes are lossless by the NEW general retyping theorem. -/
theorem private_equivalent (r : Role) : ContextEquivalent (Ω r) (K r) := by
  intro x
  cases r <;>
    by_cases h₀ : x = ⟨.var 0, .positive⟩ <;>
    by_cases h₁ : x = ⟨.var 0, .negative⟩ <;>
    by_cases h₂ : x = ⟨.var 1, .positive⟩ <;>
    by_cases h₃ : x = ⟨.var 1, .negative⟩
  all_goals subst_vars
  all_goals
    rw [K, Context.bind_empty, Context.bind, Context.lift_union,
      Context.lift_singleton, Context.lift_singleton] <;>
      try simp [Finmap.Disjoint, Finmap.mem_singleton]
  all_goals
    simp_all [Ω, Γ, Θ, Ψ, privatePayload, Key.mapName, liftName, e, f,
      Key.opposite, Role.opposite, Finmap.mem_singleton, Finmap.lookup_union_right]
  all_goals first
    | exact Capability.Equivalent.refl _
    | exact ⟨rfl, C_A_equiv.recvEndpoint D_equiv _ 11⟩

/-- Actual same-domain semantic balance includes independently coded peers. -/
theorem network_balanced (r : Role) : Conversion.Balanced (Ω r) :=
  ((Conversion.balanced_empty.bind (privatePayload r)).bind (c r)).retype
    (private_equivalent r).symm

/-- Actual canonical transfer and then actual received-subject communication. -/
theorem transfer : PiCalculus.Step p p₁ :=
  PiCalculus.Step.cong (Cong.symm (Cong.par_assoc _ _ _))
    (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
    (Cong.par_assoc _ _ _)

theorem use_received : PiCalculus.Step p₁ p₂ :=
  PiCalculus.Step.parR (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _))

/-- General global theorem, not a supplied frontier or ready pair. -/
theorem global_network (r : Role) : Cong p .nil ∨ ∃ q, PiCalculus.Step p q :=
  (network_ranked r).progress_balanced (network_balanced r)

/-- Process completion cannot be inferred from interface completion alone. -/
theorem network_not_nil : ¬ Cong p .nil := by
  intro hc
  exact (input_cong hc).mp (show HasUnguardedInput p from Or.inr (Or.inl trivial))

/-- Populated global result is the ACTUAL Step branch for both payload roles. -/
theorem global_actual_step (r : Role) : ∃ q, PiCalculus.Step p q := by
  rcases global_network r with hn | hs
  · exact False.elim (network_not_nil hn)
  · exact hs

/-- Nested private closure is derived by new retyping and literal dual-pair rules. -/
theorem closed_ranked (r : Role) : Conversion.RankedType 0 ∅ (.nu (.nu p)) :=
  Conversion.RankedType.nu (Conversion.RankedType.nu
    ((network_ranked r).retype (private_equivalent r)))

/-- Closed progress internally traverses every actual restriction. -/
theorem closed_global (r : Role) : Cong (.nu (.nu p)) .nil ∨ ∃ q, PiCalculus.Step (.nu (.nu p)) q :=
  (closed_ranked r).progress_empty

/-- Finite actual reachable state uses new ranked preservation then global progress. -/
theorem received_reachable_progress (r : Role) :
    Cong (.nu (.nu p₁)) .nil ∨ ∃ q, PiCalculus.Step (.nu (.nu p₁)) q :=
  (closed_ranked r).reachable_progress (Relation.ReflTransGen.refl.tail
    (PiCalculus.Step.nu (PiCalculus.Step.nu transfer)))

/-- The transferred slot is genuinely active when the guard checks it. -/
theorem active_payload_before (r : Role) : 5 < v.rank ∧ v.protocol.unfold ≠ .done := by
  constructor
  · exact (sender_guard r).active_payload_rank (d := f r) (c := v)
      (by simp [Γ, e, f, Finmap.mem_singleton]) (by intro h; cases h) (by simp [e, f])
  · intro h
    cases h

/-- Disconnected private components still use the GENERAL global theorem. -/
theorem disconnected_global (r : Role) :
    Cong (.par (.nu (.nu p)) (.nu (.nu p))) .nil ∨
      ∃ q, PiCalculus.Step (.par (.nu (.nu p)) (.nu (.nu p))) q := by
  have ht := Conversion.RankedType.par (Finmap.disjoint_empty (∅ : Context))
    (closed_ranked r) (closed_ranked r)
  simpa only [Finmap.empty_union] using ht.progress_empty

/-- Scope/swap act through ALL16 Cong and progress normalizes internally. -/
theorem swapped_global (r : Role) :
    Cong (.nu (.nu (swapProc 0 p))) .nil ∨ ∃ q, PiCalculus.Step (.nu (.nu (swapProc 0 p))) q :=
  ((Conversion.RankedType.cong_iff (Cong.nu_swap p)).mp (closed_ranked r)).progress_empty

/-- BOTH role cases call the general global theorem and actual execution. -/
theorem both_roles_global_gate (r : Role) : Conversion.RankedType 2 (Ω r) p ∧
    Conversion.Balanced (Ω r) ∧ (∃ q, PiCalculus.Step p q) ∧ PiCalculus.Step p p₁ ∧
    PiCalculus.Step p₁ p₂ :=
  ⟨network_ranked r, network_balanced r, global_actual_step r, transfer, use_received⟩

/-- The fixed interface is conversion-only even under any purported raw split. -/
theorem raw_interface_rejected (r : Role) : ¬ Endpoint.HasType 2 (Ω r) p := by
  intro h
  obtain ⟨L, R, hs, hd, ho, hi⟩ := h.par_inv
  obtain ⟨a, w, hn, hw, hh⟩ := ho.out_inv
  have hΩ : (Ω r).lookup a = some w := by
    rw [hs]
    exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hw)).trans hw
  cases a with
  | mk nm role =>
    change nm = .var 0 at hn
    subst nm
    cases role with
    | positive =>
      have he : w = c r := by simpa [Ω, Γ, e, f, Finmap.mem_singleton] using hΩ.symm
      subst w
      rcases hh with ⟨s, hh, hp⟩ | ⟨b, k, t, s, hb, hh, hv, hne, hp⟩
      · cases hh
      · obtain ⟨hr, hk, ht, htail⟩ := Protocol.sendEndpoint.inj hh
        have hbf : b = f r := by
          cases b with
          | mk bm br =>
            change bm = .var 1 at hb
            change r = br at hr
            subst bm
            subst br
            rfl
        subst b
        subst k
        subst t
        have hΩv : (Ω r).lookup (f r) = some (⟨11, A⟩ : Capability) := by
          rw [hs]
          exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hv)).trans hv
        have hev : (⟨11, A⟩ : Capability) = v := by
          cases r <;> simpa [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite,
            Finmap.mem_singleton, Finmap.lookup_union_right] using hΩv.symm
        have hab := congrArg Capability.protocol hev
        cases hab
    | negative =>
      have he : w = d r := by
        simpa [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite,
          Finmap.mem_singleton, Finmap.lookup_union_right] using hΩ.symm
      subst w
      rcases hh with ⟨s, hh, hp⟩ | ⟨b, k, t, s, hb, hh, hv, hne, hp⟩
      · cases hh
      · cases hh

def Ω₁ (r : Role) : Context := ((Ω r).insert e ⟨5, .done⟩).insert e.opposite ⟨5, D⟩

/-- General ranked head preservation keeps the actual receiver D and moved B. -/
theorem exact_transfer_ranked (r : Role) : Conversion.RankedType 2 (Ω₁ r) p₁ := by
  have hd : Finmap.Disjoint (Γ r) (Θ r) := by
    simp [Γ, Θ, e, f, Key.opposite, Role.opposite, Finmap.Disjoint, Finmap.mem_singleton]
  have hc : Conversion.Compatible ((Γ r ∪ Θ r) ∪ Ψ r) := by
    rw [Finmap.union_assoc]
    exact (network_balanced r).compatible
  obtain ⟨d', t', u, hl, hr, hh, hp, hu, ht⟩ := Conversion.ranked_endpoint_head_preservation
    (e := e) (f := f r) (c := c r) (v := v) (t := A) (s := .done) hd
    (by simp [Γ, e, f, Finmap.mem_singleton]) rfl
    (by simp [Γ, e, f, Finmap.mem_singleton]) ⟨rfl, B_A_equiv⟩
    (by simp [e, f]) (sender_residual r) (receiver_ranked r) (by change 1 < 2; decide) hc.union_left
  have hdd : d' = d r := Context.unique hl Finmap.lookup_singleton_eq
  subst d'
  have hheads : Protocol.recvEndpoint r 11 C D = .recvEndpoint r 11 t' u := hh
  obtain ⟨hrole, hpriority, hpay, htail⟩ := Protocol.recvEndpoint.inj hheads
  subst t'
  subst u
  have hf : Finmap.Disjoint (Γ r ∪ Θ r) (Ψ r) := by
    intro x hx hy
    rcases Finmap.mem_union.mp hx with hx | hx
    · have hz : Finmap.Disjoint (Γ r) (Ψ r) := by
        cases r <;> simp [Γ, Ψ, e, f, Key.opposite, Role.opposite,
          Finmap.Disjoint, Finmap.mem_singleton]
      exact hz x hx hy
    · have hz : Finmap.Disjoint (Θ r) (Ψ r) := by
        simp [Θ, Ψ, e, f, Key.opposite, Finmap.Disjoint, Finmap.mem_singleton]
      exact hz x hx hy
  have ha : Conversion.SemanticAdvance (Γ r ∪ Θ r)
      (((Γ r ∪ Θ r).insert e ⟨5, .done⟩).insert e.opposite ⟨5, D⟩) :=
    Conversion.SemanticAdvance.matched (e := e) (c := c r) (d := d r) (s := .done) (u := D)
      (by simp [Γ, Θ, e, f, Finmap.mem_singleton])
      (by simp [Γ, Θ, e, f, Key.opposite, Role.opposite, Finmap.mem_singleton])
      ⟨rfl, C_A_equiv.recvEndpoint D_equiv r 11⟩
      (Conversion.CommunicationHeads.endpoint rfl rfl C_A_equiv) D_equiv
  have hout := Conversion.RankedType.par (ha.disjoint_frame hf) ht (peer_ranked r)
  rw [← Finmap.insert_union, ← Finmap.insert_union, Finmap.union_assoc] at hout
  exact (Conversion.RankedType.cong_iff (Cong.par_assoc _ _ _)).mp hout

/-- The actual transferred B/rank11 and its peer are not normalized to advertisement A. -/
theorem transferred_actual_metadata (r : Role) : (Ω₁ r).lookup (f r) = some v ∧
    (Ω₁ r).lookup (f r).opposite = some v.dual := by
  constructor
  · rw [Ω₁, Conversion.head_update_other _ _ _ _ _ (by simp [e, f]) (by simp [e, f, Key.opposite])]
    simp [Ω, Γ, Θ, Ψ, e, f, Finmap.mem_singleton, Finmap.lookup_union_right]
  · rw [Ω₁, Conversion.head_update_other _ _ _ _ _ (by simp [e, f, Key.opposite])
      (by simp [e, f, Key.opposite])]
    cases r <;> simp [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite,
      Finmap.mem_singleton, Finmap.lookup_union_right]

/-- An input owning its opposite same-physical role cannot bypass GuardMin. -/
theorem self_wait_rejected (k : Nat) (q : Proc) : ¬ Conversion.RankedType 1
    (Context.bind (⟨k, .recvName (.sendName .done)⟩ : Capability) ∅) (.inp (.var 0) q) := by
  intro h
  obtain ⟨a, w, hn, hw, ha, hg⟩ := h.inp_active
  cases a with
  | mk nm role =>
    change nm = .var 0 at hn
    subst nm
    cases role with
    | positive =>
      have he := Context.unique hw (Context.lookup_bind_positive ⟨k, .recvName (.sendName .done)⟩ ∅)
      subst w
      exact guardMin_rejects_peer (e := ⟨.var 0, .positive⟩)
        (Context.lookup_bind_negative (⟨k, .recvName (.sendName .done)⟩ : Capability) ∅)
        (by intro he; cases he) hg
    | negative =>
      have he := Context.unique hw (Context.lookup_bind_negative ⟨k, .recvName (.sendName .done)⟩ ∅)
      subst w
      exact guardMin_rejects_peer (e := ⟨.var 0, .negative⟩)
        (Context.lookup_bind_positive (⟨k, .recvName (.sendName .done)⟩ : Capability) ∅)
        (by intro he; cases he) hg

/-- The two actual active-owned-key obligations of a cyclic wait are inconsistent. -/
theorem cyclic_guard_rejected (k l : Nat) : ¬
    (GuardMin ((Finmap.singleton e (⟨k, .recvName .done⟩ : Capability)).insert (f .positive)
      ⟨l, .sendName .done⟩) e k ∧
     GuardMin ((Finmap.singleton (f .negative) (⟨l, .recvName .done⟩ : Capability)).insert
       e.opposite ⟨k, .sendName .done⟩) (f .negative) l) := by
  rintro ⟨ha, hb⟩
  have h₁ := ha (f .positive) ⟨l, .sendName .done⟩ (Finmap.lookup_insert _)
    (by intro h; cases h) (by simp [e, f])
  have h₂ := hb e.opposite ⟨k, .sendName .done⟩ (Finmap.lookup_insert _)
    (by intro h; cases h) (by simp [e, f, Key.opposite])
  exact Nat.lt_asymm h₁ h₂

def waitLeft (k l : Nat) : Context := (Finmap.singleton e
  (⟨k, .recvName .done⟩ : Capability)).insert (f .positive) ⟨l, .sendName .done⟩
def waitRight (k l : Nat) : Context := (Finmap.singleton (f .negative)
  (⟨l, .recvName .done⟩ : Capability)).insert e.opposite ⟨k, .sendName .done⟩

/-- No rank assignment can type both actual cyclic-wait input owners. -/
theorem cyclic_ranked_rejected (k l : Nat) (q q' : Proc) : ¬
    (Conversion.RankedType 2 (waitLeft k l) (.inp (.var 0) q) ∧
      Conversion.RankedType 2 (waitRight k l) (.inp (.var 1) q')) := by
  rintro ⟨ha, hb⟩
  obtain ⟨a, ca, hna, hca, haa, hga⟩ := ha.inp_active
  have hae : a = e := by
    rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hca) with he | he
    · subst a
      cases hna
    · exact (Finmap.mem_singleton _ _ _).mp he
  subst a
  have hcap : ca = ⟨k, .recvName .done⟩ := by
    simpa [waitLeft, e, f] using hca.symm
  subst ca
  obtain ⟨b, cb, hnb, hcb, hab, hgb⟩ := hb.inp_active
  have hbf : b = f .negative := by
    rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hcb) with he | he
    · subst b
      cases hnb
    · exact (Finmap.mem_singleton _ _ _).mp he
  subst b
  have hcap : cb = ⟨l, .recvName .done⟩ := by
    simpa [waitRight, e, f, Key.opposite] using hcb.symm
  subst cb
  exact cyclic_guard_rejected k l ⟨hga, hgb⟩

def completedFrame : Context := Context.bind (⟨13, D⟩ : Capability) ∅

/-- Actual completed graph roles can form a balanced, nonempty external frame. -/
theorem completed_frame_nil : Conversion.RankedType 1 completedFrame .nil := by
  have hn : Conversion.RankedType 1 (∅ : Context) .nil :=
    Conversion.RankedType.nil Context.completed_empty
      (fun _ hx => False.elim (Finmap.notMem_empty hx))
  have hp := hn.weaken_completed (z := ⟨.var 0, .positive⟩) (u := ⟨13, D⟩)
    Finmap.notMem_empty D_done (Nat.zero_lt_succ 0)
  have hm := hp.weaken_completed (z := ⟨.var 0, .negative⟩) (u := (⟨13, D⟩ : Capability).dual)
    (by simp [Finmap.mem_insert, Finmap.notMem_empty]) rfl (Nat.zero_lt_succ 0)
  simpa only [completedFrame, Context.bind, Context.lift_empty] using hm

/-- Global progress covers a disconnected completed-role frame at a nonempty interface. -/
theorem completed_frame_global (r : Role) :
    Cong (.par (liftProc 0 (.nu (.nu p))) .nil) .nil ∨
      ∃ q, PiCalculus.Step (.par (liftProc 0 (.nu (.nu p))) .nil) q := by
  have ht := Conversion.RankedType.par (Finmap.disjoint_empty completedFrame)
    ((closed_ranked r).lift 0) completed_frame_nil
  rw [Finmap.empty_union] at ht
  exact ht.progress_balanced (Conversion.balanced_empty.bind ⟨13, D⟩)

/-- Actual scope extrusion is handled by new all-Cong then genuine global progress. -/
theorem scope_global (r : Role) : Cong (.nu (.par (.nu p) .nil)) .nil ∨
    ∃ q, PiCalculus.Step (.nu (.par (.nu p) .nil)) q := by
  have hn : Conversion.RankedType 0 (∅ : Context) .nil :=
    Conversion.RankedType.nil Context.completed_empty
      (fun _ hx => False.elim (Finmap.notMem_empty hx))
  have ht := Conversion.RankedType.par (Finmap.disjoint_empty (∅ : Context)) (closed_ranked r) hn
  rw [Finmap.empty_union] at ht
  exact ((Conversion.RankedType.cong_iff (Cong.scope (.nu p) .nil)).mp ht).progress_empty

/-- Full ranked preservation is applied to BOTH actual private communications. -/
theorem closed_after_both (r : Role) : Conversion.RankedType 0 ∅ (.nu (.nu p₂)) :=
  Conversion.RankedType.subject_reduction_empty
    ((closed_ranked r).subject_reduction_empty (PiCalculus.Step.nu (PiCalculus.Step.nu transfer)))
    (PiCalculus.Step.nu (PiCalculus.Step.nu use_received))

/-- The completion alternative is actual process Cong nil, not a completed empty map. -/
theorem completed_process_nil : Cong (.nu (.nu p₂)) .nil := by
  have hp : Cong p₂ .nil := Cong.trans (Cong.par_cong (Cong.refl _)
    (Cong.par_nil .nil)) (Cong.par_nil .nil)
  exact Cong.trans (Cong.nu_cong (Cong.nu_cong hp))
    (Cong.trans (Cong.nu_cong Cong.nu_nil) Cong.nu_nil)

/-- The general global theorem is consumed on the reached completed process too. -/
theorem completed_global (r : Role) : Cong (.nu (.nu p₂)) .nil ∨
    ∃ q, PiCalculus.Step (.nu (.nu p₂)) q := (closed_after_both r).progress_empty

end Cslib.SessionTypes.Endpoint.RankedConversionTests
