/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.ConversionReduction

/-!
# Full-Cong/full-Step consumers with conversion-only fixed interfaces

The private fixture uses actual nested restrictions. A payload hidden by
one binder is not falsely claimed to be owned by an outer clock relation.
-/

namespace Cslib.SessionTypes.Endpoint.ConversionPreservationTests

open PiCalculus

def g : Graph := ⟨2, fun i => if i.val = 0 then .sendName ⟨1, by decide⟩ else .done⟩
def B : Protocol := .regular g ⟨0, by decide⟩ false
def D : Protocol := .regular g ⟨1, by decide⟩ false
def C : Protocol := .sendName D
def A : Protocol := .sendName .done
def e : Key := ⟨.var 1, .positive⟩
def f (r : Role) : Key := ⟨.var 0, r⟩
def v : Capability := ⟨11, B⟩
def c (r : Role) : Capability := ⟨5, .sendEndpoint r 11 A .done⟩
def d (r : Role) : Capability := ⟨5, .recvEndpoint r 11 C D⟩
def Γ (r : Role) : Context := Finmap.singleton e (c r) ∪ Finmap.singleton (f r) v
def Θ (r : Role) : Context := Finmap.singleton e.opposite (d r)
def Ψ (r : Role) : Context := Finmap.singleton (f r).opposite v.dual
def Ω (r : Role) : Context := Γ r ∪ (Θ r ∪ Ψ r)
def snd : Proc := .out e.name (.var 0) .nil
def rcv : Proc := .inp e.name (.out (.var 0) (.const 199) .nil)
def peer : Proc := .inp (.var 0) .nil
def p : Proc := .par snd (.par rcv peer)
def p₁ : Proc := .par .nil (.par (.out (.var 0) (.const 199) .nil) peer)
def p₂ : Proc := .par .nil (.par .nil .nil)

theorem D_done : D.unfold = .done := rfl

theorem D_equiv : D.TreeEquiv .done := Protocol.treeEquiv_iff_head.mpr HeadMatch.done

theorem C_equiv : C.TreeEquiv A := D_equiv.sendName

theorem B_C_equiv : B.TreeEquiv C := B.treeEquiv_unfold

theorem B_A_equiv : B.TreeEquiv A := B_C_equiv.trans C_equiv

theorem c_d_equiv (r : Role) : (d r).Equivalent (c r).dual :=
  ⟨rfl, C_equiv.recvEndpoint D_equiv r 11⟩

private theorem pair_balanced (a : Key) (x y : Capability) (he : y.Equivalent x.dual) :
    Conversion.Balanced (Finmap.singleton a x ∪ Finmap.singleton a.opposite y : Context) := by
  intro z u hu
  rcases Finmap.mem_lookup_union'.mp hu with hu | ⟨hn, hu⟩
  · have hz := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hu)
    subst z
    simp only [Finmap.lookup_singleton_eq, Option.mem_def, Option.some.injEq] at hu
    subst u
    exact ⟨y, (Finmap.lookup_union_right (by simp [Finmap.mem_singleton, Key.opposite_ne])).trans
      Finmap.lookup_singleton_eq, he⟩
  · have hz := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hu)
    subst z
    simp only [Finmap.lookup_singleton_eq, Option.mem_def, Option.some.injEq] at hu
    subst u
    have hr : x.Equivalent y.dual := by
      simpa only [Capability.dual_dual] using he.dual.symm
    exact ⟨x, by
      rw [Key.opposite_opposite, Finmap.lookup_union_left (by simp)]
      exact Finmap.lookup_singleton_eq, hr⟩

theorem split₁ (r : Role) : Finmap.Disjoint (Γ r) (Θ r ∪ Ψ r) := by
  cases r <;> simp [Γ, Θ, Ψ, e, f, Finmap.Disjoint, Finmap.mem_singleton,
    Key.opposite, Role.opposite]

theorem split₂ (r : Role) : Finmap.Disjoint (Θ r) (Ψ r) := by
  simp [Θ, Ψ, e, f, Finmap.Disjoint, Finmap.mem_singleton, Key.opposite]

theorem source_balanced (r : Role) : Conversion.Balanced (Ω r) := by
  let E : Context := Finmap.singleton e (c r)
  let F : Context := Finmap.singleton (f r) v
  have hc := pair_balanced e (c r) (d r) (c_d_equiv r)
  have hv := pair_balanced (f r) v v.dual (Capability.Equivalent.refl _)
  have hfc : Finmap.Disjoint F (Θ r) := by
    simp [F, Θ, e, f, Finmap.Disjoint, Finmap.mem_singleton, Key.opposite]
  have hboth : Finmap.Disjoint (E ∪ Θ r) (F ∪ Ψ r) := by
    cases r <;> simp [E, F, Θ, Ψ, e, f, Finmap.Disjoint, Finmap.mem_singleton, Key.opposite]
  have heq : Ω r = (E ∪ Θ r) ∪ (F ∪ Ψ r) := by
    change (E ∪ F) ∪ (Θ r ∪ Ψ r) = _
    rw [Finmap.union_assoc, ← Finmap.union_assoc (s₁ := F), Finmap.union_comm_of_disjoint hfc,
      Finmap.union_assoc (s₁ := Θ r), ← Finmap.union_assoc (s₁ := E)]
  rw [heq]
  exact hc.union hv hboth

private theorem sender_body (r : Role) : Conversion.HasType 2
    (((Γ r).erase (f r)).insert e ⟨5, .done⟩) .nil := by
  apply Conversion.HasType.nil
  · intro z u hz
    by_cases he : z = e
    · subst z
      rw [Finmap.lookup_insert] at hz
      cases hz
      rfl
    · rw [Finmap.lookup_insert_of_ne _ he] at hz
      by_cases hf : z = f r
      · subst z
        rw [Finmap.lookup_erase] at hz
        cases hz
      · rw [Finmap.lookup_erase_ne hf] at hz
        have hnone : z ∉ Γ r := by simp [Γ, Finmap.mem_singleton, he, hf]
        rw [Finmap.lookup_eq_none.mpr hnone] at hz
        cases hz
  · intro z hz
    rcases Finmap.mem_insert.mp hz with rfl | hz
    · change 1 < 2
      decide
    · rcases Finmap.mem_union.mp (Finmap.mem_erase.mp hz).2 with hz | hz
      · have he := (Finmap.mem_singleton _ _ _).mp hz
        subst z
        change 1 < 2
        decide
      · have he := (Finmap.mem_singleton _ _ _).mp hz
        subst z
        exact Nat.zero_lt_succ 1

private theorem rcv_typed (r : Role) : Conversion.HasType 2 (Θ r) rcv := by
  apply Conversion.HasType.inpEndpoint (e := e.opposite) (c := d r) (r := r)
    (k := 11) (t := C) (s := D)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · change 1 < 2
    decide
  · rw [Θ, Finmap.insert_singleton_eq, Context.lift_singleton]
    apply Conversion.HasType.outName (e := ⟨.var 0, r⟩) (c := ⟨11, C⟩) (s := D)
    · exact Finmap.lookup_insert _
    · rfl
    · exact Nat.zero_lt_succ 2
    · trivial
    · rw [Finmap.insert_insert]
      apply Conversion.HasType.nil
      · intro z u hz
        by_cases he : z = ⟨.var 0, r⟩
        · subst z
          rw [Finmap.lookup_insert] at hz
          cases hz
          rfl
        · rw [Finmap.lookup_insert_of_ne _ he] at hz
          have hk := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hz)
          subst z
          simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hz
          subst u
          rfl
      · intro z hz
        rcases Finmap.mem_insert.mp hz with rfl | hz
        · exact Nat.zero_lt_succ 2
        · have hk := (Finmap.mem_singleton _ _ _).mp hz
          subst z
          change 2 < 3
          decide

private theorem peer_typed (r : Role) : Conversion.HasType 2 (Ψ r) peer := by
  apply Conversion.HasType.inpName (e := (f r).opposite) (c := v.dual) (s := D.dual)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Nat.zero_lt_succ 1
  · rw [Ψ, Finmap.insert_singleton_eq, Context.lift_singleton]
    exact Conversion.HasType.of_raw (Endpoint.HasType.nil_singleton_completed
      (by change 1 < 3; decide) rfl)

theorem source_typed (r : Role) : Conversion.HasType 2 (Ω r) p := by
  apply Conversion.HasType.par (split₁ r)
  · apply Conversion.HasType.outEndpoint (e := e) (d := f r)
      (c := c r) (v := v) (k := 11) (t := A) (s := .done)
    · exact (Finmap.lookup_union_left (by simp)).trans Finmap.lookup_singleton_eq
    · rfl
    · exact (Finmap.lookup_union_right (by simp [e, f, Finmap.mem_singleton])).trans
        Finmap.lookup_singleton_eq
    · exact ⟨rfl, B_A_equiv⟩
    · simp [e, f]
    · change 1 < 2
      decide
    · exact Nat.zero_lt_succ 1
    · exact sender_body r
  · exact Conversion.HasType.par (split₂ r) (rcv_typed r) (peer_typed r)

theorem transfer : PiCalculus.Step p p₁ :=
  PiCalculus.Step.cong (Cong.symm (Cong.par_assoc _ _ _))
    (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
    (Cong.par_assoc _ _ _)

theorem use_received : PiCalculus.Step p₁ p₂ :=
  PiCalculus.Step.parR (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _))

/-- FULL five-case theorem is instantiated on the actual congruence-framed transfer. -/
theorem full_step_transfer (r : Role) : ∃ Ξ, Conversion.HasType 2 Ξ p₁ ∧
    Conversion.Compatible Ξ ∧ (Ξ = Ω r ∨ Conversion.SemanticAdvance (Ω r) Ξ) :=
  (source_typed r).subject_reduction (source_balanced r).compatible transfer

/-- Balance follows the full theorem on the same actual conversion-only derivation. -/
theorem full_balanced_transfer (r : Role) : ∃ Ξ, Conversion.HasType 2 Ξ p₁ ∧
    Conversion.Balanced Ξ ∧ (Ξ = Ω r ∨ Conversion.SemanticAdvance (Ω r) Ξ) :=
  (source_typed r).subject_reduction_balanced (source_balanced r) transfer

def K (r : Role) : Context := Context.bind
  (match r with | .positive => v | .negative => v.dual) (Context.bind (c r) ∅)

private theorem lookup_singleton_ne (a x : Key) (c : Capability) (h : x ≠ a) :
    (Finmap.singleton a c : Context).lookup x = none :=
  Finmap.lookup_eq_none.mpr (by simpa using h)

attribute [local simp] lookup_singleton_ne Finmap.lookup_singleton_eq

/-- Retyping uses the chosen literal private pairs, not a raw-typing admission wrapper. -/
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
    simp_all [Ω, Γ, Θ, Ψ, Key.mapName, liftName, e, f, Key.opposite, Role.opposite,
      Finmap.mem_singleton, Finmap.lookup_union_right]
  all_goals first | exact Capability.Equivalent.refl _ | exact c_d_equiv _

/-- Actual two-restriction process, with the literal chosen-pair typing rules. -/
theorem closed_typed (r : Role) : Conversion.HasType 0 ∅ (.nu (.nu p)) :=
  Conversion.HasType.nu (Conversion.HasType.nu ((source_typed r).retype (private_equivalent r)))

/-- Transfer passes through an outer advancement projection then an internal one. -/
theorem closed_transfer (r : Role) : Conversion.HasType 0 ∅ (.nu (.nu p₁)) :=
  (closed_typed r).subject_reduction_empty (PiCalculus.Step.nu (PiCalculus.Step.nu transfer))

/-- The actual received subject communicates under the same two private binders. -/
theorem closed_use_received (r : Role) : Conversion.HasType 0 ∅ (.nu (.nu p₂)) :=
  (closed_transfer r).subject_reduction_empty (PiCalculus.Step.nu (PiCalculus.Step.nu use_received))

/-- Finite canonical execution calls general safety, not a manually typed tail. -/
theorem two_steps_closed (r : Role) : Conversion.HasType 0 ∅ (.nu (.nu p₂)) :=
  (closed_typed r).reachable_empty ((Relation.ReflTransGen.refl.tail
    (PiCalculus.Step.nu (PiCalculus.Step.nu transfer))).tail
      (PiCalculus.Step.nu (PiCalculus.Step.nu use_received)))

/-- Full congruence invariance transports the live two-binder source through swap. -/
theorem swapped_closed (r : Role) : Conversion.HasType 0 ∅ (.nu (.nu (swapProc 0 p))) :=
  (Conversion.HasType.cong_iff (Cong.nu_swap p)).mp (closed_typed r)

def Ω₁ (r : Role) : Context := ((Ω r).insert e ⟨5, .done⟩).insert e.opposite ⟨5, D⟩

/-- Literal exact external carrier update, with independently coded receiver tail. -/
theorem exact_transfer_advance (r : Role) : Conversion.SemanticAdvance (Ω r) (Ω₁ r) := by
  apply Conversion.SemanticAdvance.matched (e := e) (c := c r) (d := d r)
  · simp [Ω, Γ, e, f, Finmap.mem_singleton]
  · simp [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite, Finmap.mem_singleton]
  · exact c_d_equiv r
  · exact Conversion.CommunicationHeads.endpoint rfl rfl C_equiv
  · exact D_equiv

/-- Payload B and its peer remain actual frame VALUES, including enclosing rank11. -/
theorem payload_frame_exact (r : Role) : (Ω₁ r).lookup (f r) = some v ∧
    (Ω₁ r).lookup (f r).opposite = some v.dual := by
  constructor
  · rw [Ω₁, Conversion.head_update_other _ _ _ _ _ (by simp [e, f]) (by simp [e, f, Key.opposite])]
    simp [Ω, Γ, Θ, Ψ, e, f, Finmap.mem_singleton, Finmap.lookup_union_right]
  · rw [Ω₁, Conversion.head_update_other _ _ _ _ _ (by simp [e, f, Key.opposite])
      (by simp [e, f, Key.opposite])]
    cases r <;> simp [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite,
      Finmap.mem_singleton, Finmap.lookup_union_right]

/-- General endpoint preservation and full Cong produce the exact operational map. -/
theorem exact_transfer_typed (r : Role) : Conversion.HasType 2 (Ω₁ r) p₁ := by
  have hd : Finmap.Disjoint (Γ r) (Θ r) := by
    intro x hx ht
    exact split₁ r x hx (Finmap.mem_union.mpr (Or.inl ht))
  have hc : Conversion.Compatible ((Γ r ∪ Θ r) ∪ Ψ r) := by
    rw [Finmap.union_assoc]
    exact (source_balanced r).compatible
  obtain ⟨d', t', u, hl, hr, hh, hp, hu, ht⟩ := Conversion.endpoint_head_preservation
    (e := e) (f := f r) (c := c r) (v := v) (t := A) (s := .done) hd
    (by simp [Γ, e, f, Finmap.mem_singleton]) rfl
    (by simp [Γ, e, f, Finmap.mem_singleton]) ⟨rfl, B_A_equiv⟩
    (by simp [e, f]) (sender_body r) (rcv_typed r) (Nat.zero_lt_succ 1) hc.union_left
  have he : d' = d r := Context.unique hl Finmap.lookup_singleton_eq
  subst d'
  have hheads : Protocol.recvEndpoint r 11 C D = .recvEndpoint r 11 t' u := hh
  obtain ⟨hrole, hpriority, hpayload, htail⟩ := Protocol.recvEndpoint.inj hheads
  subst t'
  subst u
  have hf : Finmap.Disjoint (Γ r ∪ Θ r) (Ψ r) := by
    intro x hx hy
    rcases Finmap.mem_union.mp hx with hx | hx
    · exact split₁ r x hx (Finmap.mem_union.mpr (Or.inr hy))
    · exact split₂ r x hx hy
  have ha : Conversion.SemanticAdvance (Γ r ∪ Θ r)
      (((Γ r ∪ Θ r).insert e ⟨5, .done⟩).insert e.opposite ⟨5, D⟩) :=
    Conversion.SemanticAdvance.matched
      (by simp [Γ, Θ, e, f, Finmap.mem_singleton])
      (by simp [Γ, Θ, e, f, Key.opposite, Role.opposite, Finmap.mem_singleton])
      (c_d_equiv r) (Conversion.CommunicationHeads.endpoint rfl rfl C_equiv) D_equiv
  have hout := Conversion.HasType.par (ha.disjoint_frame hf) ht (peer_typed r)
  rw [← Finmap.insert_union, ← Finmap.insert_union, Finmap.union_assoc] at hout
  exact (Conversion.HasType.cong_iff (Cong.par_assoc _ _ _)).mp hout

/-- The sender's actual payload code is unequal to its fixed advertised code. -/
theorem raw_same_interface_rejected (r : Role) : ¬ Endpoint.HasType 2 (Ω r) p := by
  intro h
  obtain ⟨Γ', Θ', heq, hd, hs, ht⟩ := h.par_inv
  obtain ⟨a, w, hn, hw, hh⟩ := hs.out_inv
  have hwhole : (Γ' ∪ Θ').lookup a = some w :=
    (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hw)).trans hw
  rw [← heq] at hwhole
  cases a with
  | mk name role =>
    change name = .var 1 at hn
    subst name
    cases role with
    | positive =>
      have he : w = c r := by
        simpa [Ω, Γ, Θ, Ψ, e, f, Finmap.mem_singleton] using hwhole.symm
      subst w
      rcases hh with ⟨s, hhead, hbody⟩ | ⟨b, k, t, s, hb, hhead, hlookup, hne, hbody⟩
      · cases hhead
      · obtain ⟨hr, hk, htype, htail⟩ := Protocol.sendEndpoint.inj hhead
        have hf : b = f r := by
          cases b with
          | mk nm rl =>
            change nm = .var 0 at hb
            change r = rl at hr
            subst nm
            subst rl
            rfl
        subst b
        subst k
        subst t
        have hp : (Γ' ∪ Θ').lookup (f r) = some (⟨11, A⟩ : Capability) :=
          (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hlookup)).trans hlookup
        rw [← heq] at hp
        have hv : (⟨11, A⟩ : Capability) = v := by
          cases r <;> simpa [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite,
            Finmap.mem_singleton, Finmap.lookup_union_right] using hp.symm
        have hab : A = B := congrArg Capability.protocol hv
        cases hab
    | negative =>
      have he : w = d r := by
        simpa [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite,
          Finmap.mem_singleton, Finmap.lookup_union_right] using hwhole.symm
      subst w
      rcases hh with ⟨s, hhead, hbody⟩ | ⟨b, k, t, s, hb, hhead, hlookup, hne, hbody⟩
      · cases hhead
      · cases hhead

def O (r : Role) : Context := Context.bind (c r) ∅
def O' : Context := Context.bind (⟨5, .done⟩ : Capability) ∅

/-- Only the original chosen literal-dual pair uses the raw advancement bridge. -/
theorem outer_clock (r : Role) : Conversion.SemanticAdvance (O r) O' := by
  have hraw := DualAdvance.matched (Context.lookup_bind_positive (c r) ∅)
    (Context.lookup_bind_negative (c r) ∅) (Or.inr ⟨r, 11, A, rfl⟩)
  change DualAdvance (Context.bind (c r) ∅)
    (((Context.bind (c r) ∅).insert ⟨.var 0, .positive⟩ (⟨5, .done⟩ : Capability)).insert
      ⟨.var 0, .negative⟩ (⟨5, .done⟩ : Capability).dual) at hraw
  rw [Context.update_bound_positive] at hraw
  exact Conversion.SemanticAdvance.of_raw hraw

/-- The outer clock has no rank11 payload slot, despite its endpoint head. -/
theorem no_external_payload (r : Role) (x : Key) : (O r).lookup x ≠ some v := by
  intro hx
  rw [O, Context.bind_empty] at hx
  rcases Finmap.mem_lookup_union'.mp hx with hx | ⟨hn, hx⟩
  all_goals
    have hk := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hx)
    subst x
    rw [Finmap.lookup_singleton_eq] at hx
    have hc := congrArg Capability.rank (Option.some.inj hx)
    cases hc

/-- A hidden payload pair is unchanged by the actual lifted external action. -/
theorem lifted_outer_clock (r : Role) : Conversion.SemanticAdvance (K r)
    (Context.bind (match r with | .positive => v | .negative => v.dual) O') :=
  (outer_clock r).bind_outer _

/-- Compiled projection consumer exposes private OR exact outer evidence. -/
theorem exact_projection_consumer (r : Role) :
    (∃ w, w.rank = 11 ∧ Conversion.SemanticAdvance
      (Context.bind (match r with | .positive => v | .negative => v.dual) ∅)
      (Context.bind w ∅) ∧
      Context.bind (match r with | .positive => v | .negative => v.dual) O' =
        Context.bind w (O r)) ∨
    (∃ Δ, Conversion.SemanticAdvance (O r) Δ ∧
      Context.bind (match r with | .positive => v | .negative => v.dual) O' =
        Context.bind (match r with | .positive => v | .negative => v.dual) Δ) := by
  cases r with
  | positive => exact (lifted_outer_clock .positive).project_bind
  | negative => exact (lifted_outer_clock .negative).project_bind

/-- The full Step theorem consumes the actual received-subject second step. -/
theorem full_step_received (r : Role) : ∃ Ξ, Conversion.HasType 2 Ξ p₂ ∧
    Conversion.Compatible Ξ ∧ (Ξ = Ω₁ r ∨ Conversion.SemanticAdvance (Ω₁ r) Ξ) :=
  (exact_transfer_typed r).subject_reduction
    ((exact_transfer_advance r).compatible (source_balanced r).compatible) use_received

/-- Every actual owned key has the same enclosing rank in this concrete advance. -/
theorem all_frame_ranks (r : Role) (x : Key) (a b : Capability)
    (ha : (Ω r).lookup x = some a) (hb : (Ω₁ r).lookup x = some b) : a.rank = b.rank :=
  (exact_transfer_advance r).rank_lookup ha hb

/-- Full congruence scope extrusion wraps the connected network with an idle frame. -/
theorem scope_source (r : Role) : Conversion.HasType 0 ∅ (.nu (.par (.nu p) .nil)) := by
  have h : Conversion.HasType 0 ∅ (.par (.nu (.nu p)) .nil) := by
    have hn : Conversion.HasType 0 (∅ : Context) .nil :=
      Conversion.HasType.nil Context.completed_empty
        (fun _ hx => False.elim (Finmap.notMem_empty hx))
    have ht := Conversion.HasType.par (Finmap.disjoint_empty (∅ : Context)) (closed_typed r) hn
    simpa only [Finmap.empty_union] using ht
  exact (Conversion.HasType.cong_iff (Cong.scope (.nu p) .nil)).mp h

/-- Actual Step pre/post scope congruence is handled by full empty-interface safety. -/
theorem scope_step (r : Role) : Conversion.HasType 0 ∅ (.nu (.par (.nu p₁) .nil)) :=
  (scope_source r).subject_reduction_empty (PiCalculus.Step.cong
    (Cong.symm (Cong.scope (.nu p) .nil))
    (PiCalculus.Step.parL (PiCalculus.Step.nu (PiCalculus.Step.nu transfer)))
    (Cong.scope (.nu p₁) .nil))

/-- Actual swap-congruence-wrapped communication uses the full five-case theorem. -/
theorem swapped_step (r : Role) : Conversion.HasType 0 ∅ (.nu (.nu (swapProc 0 p₁))) :=
  (swapped_closed r).subject_reduction_empty (PiCalculus.Step.cong (Cong.symm (Cong.nu_swap p))
    (PiCalculus.Step.nu (PiCalculus.Step.nu transfer)) (Cong.nu_swap p₁))

/-- Semantic carrier peer codes are NOT original literal duals. -/
theorem raw_peer_premise_rejected (r : Role) : (Ω r).lookup e.opposite ≠ some (c r).dual := by
  intro hx
  have hd : (Ω r).lookup e.opposite = some (d r) := by
    simp [Ω, Γ, Θ, Ψ, e, f, Key.opposite, Role.opposite, Finmap.mem_singleton]
  have he := congrArg (fun w : Capability => w.protocol.unfold) (Context.unique hd hx)
  have hh : Protocol.recvEndpoint r 11 C D = .recvEndpoint r 11 A .done := he
  have ht := (Protocol.recvEndpoint.inj hh).2.2.2
  cases ht

/-- A completed graph slot, not the literal done constructor, weakens a live network. -/
theorem completed_graph_frame (r : Role) : Conversion.HasType 0
    ((∅ : Context).insert ⟨.const 777, .negative⟩ ⟨13, D⟩) (.nu (.nu p)) :=
  (closed_typed r).weaken_completed Finmap.notMem_empty D_done trivial

/-- Erasure needs real absence in every syntax position, including payloads. -/
theorem absent_completed_frame (r : Role) : Conversion.HasType 0
    (((∅ : Context).insert ⟨.const 777, .negative⟩ ⟨13, D⟩).erase ⟨.const 777, .negative⟩)
    (.nu (.nu p)) := by
  apply (completed_graph_frame r).erase_nameAbsent
  simp [NameAbsent, p, snd, rcv, peer, e, liftName]

/-- Literal independent cap-rank mismatch is never justified by tree equivalence. -/
theorem cap_rank_mismatch : ¬ (⟨12, B⟩ : Capability).Equivalent ⟨11, C⟩ := by
  intro h
  cases h.1

/-- Wrong endpoint payload role remains a literal head observation. -/
theorem payload_role_mismatch : ¬ (Protocol.sendEndpoint .positive 11 A D).TreeEquiv
    (.sendEndpoint .negative 11 A D) := by
  intro h
  have hh := h.head
  cases hh

/-- A genuinely internal pair leaves the external empty map unchanged. -/
theorem internal_projection_only (r : Role) : ∃ w, w.rank = 5 ∧
    Conversion.SemanticAdvance (Context.bind (c r) ∅) (Context.bind w ∅) ∧
      O' = Context.bind w ∅ := by
  rcases (outer_clock r).project_bind with hi | ⟨Δ, ha, he⟩
  · exact hi
  · cases ha with
    | matched hl => simp at hl

/-- The lifted selected subject is external: an internal-only explanation is refuted. -/
theorem external_projection_only (r : Role) : ∃ Δ, Conversion.SemanticAdvance (O r) Δ ∧
    Context.bind (match r with | .positive => v | .negative => v.dual) O' =
      Context.bind (match r with | .positive => v | .negative => v.dual) Δ := by
  rcases (lifted_outer_clock r).project_bind with ⟨w, hr, ha, he⟩ | ho
  · have hs : (Context.bind w (O r)).lookup ⟨.var 1, .positive⟩ = some (c r) :=
      Context.lookup_bind_outer.mpr (Context.lookup_bind_positive (c r) ∅)
    have ht := (congrArg (fun Γ : Context => Γ.lookup ⟨.var 1, .positive⟩) he).trans hs
    have hp : O'.lookup ⟨.var 0, .positive⟩ = some (c r) := Context.lookup_bind_outer.mp ht
    have hh := congrArg Capability.protocol
      (Context.unique hp (Context.lookup_bind_positive (⟨5, .done⟩ : Capability) ∅))
    cases hh
  · exact ho

end Cslib.SessionTypes.Endpoint.ConversionPreservationTests
