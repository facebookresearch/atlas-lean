/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Fintype.Card

/-!
# Overwrite-sample register

A memory-mapped sample register as a labeled transition system
over `Cslib.LTS`: publishes overwrite the slot, reads return the
current contents. Publication IDs carried on the publish event
are ghost state. Under strictly increasing publish IDs, every
read returns the value of a specific earlier publish, read IDs
are strictly increasing, and an unread publish is either still
in the slot or was overwritten before any later read. With
decreasing publish IDs the monotonicity fails.
-/

@[expose] public section

universe u v

namespace Cslib.Semantics.Peripheral.OverwriteSampleRegister

/-- Register state: `none` (empty) or `some (id, value)`. -/
abbrev Slot (α : Type u) : Type u := Option (ℕ × α)

/-- Observable events: a publication of value `value` under ghost ID `id`, or a read that
returned `result`. -/
inductive Label (α : Type u) : Type u where
  | publish (id : ℕ) (value : α)
  | read (result : Option (ℕ × α))

/-- Transition relation of the overwrite-newest single-slot register. `publish` overwrites
the slot; `read` is enabled only when its result is the current slot, and clears it. -/
inductive RegisterStep {α : Type u} : Slot α → Label α → Slot α → Prop where
  | publish (s : Slot α) (n : ℕ) (v : α) : RegisterStep s (.publish n v) (some (n, v))
  | read (s : Slot α) : RegisterStep s (.read s) none

/-- The register as a `Cslib.LTS`. -/
def registerLTS (α : Type u) : Cslib.LTS (Slot α) (Label α) where
  Tr := RegisterStep

/-- IDs of the publications in a trace, in order. -/
def publishIds {α : Type u} (μs : List (Label α)) : List ℕ :=
  μs.filterMap fun
    | .publish n _ => some n
    | .read _ => none

/-- IDs returned by the successful reads in a trace, in order. -/
def readIds {α : Type u} (μs : List (Label α)) : List ℕ :=
  μs.filterMap fun
    | .read (some (n, _)) => some n
    | _ => none

/-! ### Specification of the two operations -/

/-- `publish n v` overwrites whatever is in the slot. -/
theorem registerLTS_tr_publish_iff {α : Type u} (s s' : Slot α) (n : ℕ) (v : α) :
    (registerLTS α).Tr s (.publish n v) s' ↔ s' = some (n, v) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact RegisterStep.publish _ _ _

/-- An atomic read returns exactly the current slot and clears it. -/
theorem registerLTS_tr_read_iff {α : Type u} (s s' : Slot α) (r : Option (ℕ × α)) :
    (registerLTS α).Tr s (.read r) s' ↔ r = s ∧ s' = none := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact RegisterStep.read _

/-! ### Private helpers (not part of the pin) -/

/-- IDs exposed by a slot: the stored ID, or nothing when empty. -/
private def slotIds {α : Type u} : Slot α → List ℕ
  | none => []
  | some (n, _) => [n]

private theorem slotIds_none {α : Type u} : slotIds (none : Slot α) = [] := rfl

private theorem slotIds_some {α : Type u} (n : ℕ) (v : α) :
    slotIds (some (n, v) : Slot α) = [n] := rfl

private theorem readIds_publish_eq {α : Type u} (μs : List (Label α)) (n : ℕ) (v : α) :
    readIds (Label.publish n v :: μs) = readIds μs := rfl

private theorem readIds_read_some_eq {α : Type u} (μs : List (Label α)) (n : ℕ) (v : α) :
    readIds (Label.read (some (n, v)) :: μs) = n :: readIds μs := rfl

private theorem readIds_read_none_eq {α : Type u} (μs : List (Label α)) :
    readIds (Label.read none :: μs) = readIds μs := rfl

private theorem publishIds_publish_eq {α : Type u} (μs : List (Label α)) (n : ℕ) (v : α) :
    publishIds (Label.publish n v :: μs) = n :: publishIds μs := rfl

private theorem publishIds_read_eq {α : Type u} (μs : List (Label α))
    (r : Option (ℕ × α)) :
    publishIds (Label.read r :: μs) = publishIds μs := rfl

/-- Single-step case of `mtr_slot_sublist`, with the start state named. -/
private theorem mtr_slot_sublist_step {α : Type u} (s₁ : Slot α) (mu : Label α)
    (tl : List (Label α)) (s₂ : Slot α) (htr : (registerLTS α).Tr s₁ mu s₂)
    (ih : (readIds tl).Sublist (slotIds s₂ ++ publishIds tl)) :
    (readIds (mu :: tl)).Sublist (slotIds s₁ ++ publishIds (mu :: tl)) := by
  cases htr with
  | publish pn pv =>
      rw [readIds_publish_eq, publishIds_publish_eq]
      rw [slotIds_some] at ih
      refine ih.trans ?_
      cases s₁ with
      | none =>
          rw [slotIds_none]
          exact List.Sublist.refl _
      | some p =>
          obtain ⟨m, w⟩ := p
          rw [slotIds_some]
          exact List.Sublist.cons m (List.Sublist.refl _)
  | read =>
      rw [publishIds_read_eq]
      rw [slotIds_none] at ih
      cases s₁ with
      | none =>
          rw [readIds_read_none_eq, slotIds_none]
          exact ih
      | some p =>
          obtain ⟨n, v⟩ := p
          rw [readIds_read_some_eq, slotIds_some]
          exact List.Sublist.cons_cons n ih

/-- General sublist fact: successful read IDs embed into the initial slot ID (if any)
followed by the publication IDs. -/
private theorem mtr_slot_sublist {α : Type u} (s₀ : Slot α) (μs : List (Label α))
    (s : Slot α) (h : (registerLTS α).MTr s₀ μs s) :
    (readIds μs).Sublist (slotIds s₀ ++ publishIds μs) := by
  induction h with
  | refl => exact List.nil_sublist _
  | stepL htr hrest ih => exact mtr_slot_sublist_step _ _ _ _ htr ih

/-- Strictly increasing lists have no duplicates. -/
private theorem nodup_of_pairwise_lt {l : List ℕ} (h : l.Pairwise (· < ·)) : l.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact h.imp (fun hab => ne_of_lt hab)

/-- Split a multistep transition over an appended label list. -/
private theorem mtr_split {α : Type u} (l₁ : List (Label α)) (s₀ : Slot α)
    {l₂ : List (Label α)} {s : Slot α} (h : (registerLTS α).MTr s₀ (l₁ ++ l₂) s) :
    ∃ mid, (registerLTS α).MTr s₀ l₁ mid ∧ (registerLTS α).MTr mid l₂ s := by
  induction l₁ generalizing s₀ with
  | nil =>
      exact ⟨s₀, Cslib.LTS.MTr.refl, h⟩
  | cons hd tl ih =>
      rw [List.cons_append] at h
      cases h with
      | stepL htr hrest =>
          obtain ⟨mid, h1, h2⟩ := ih _ hrest
          exact ⟨mid, Cslib.LTS.MTr.stepL htr h1, h2⟩

/-- A single-label multistep transition is a single step. -/
private theorem mtr_singleton {α : Type u} {s₀ : Slot α} {μ : Label α} {s : Slot α}
    (h : (registerLTS α).MTr s₀ [μ] s) : (registerLTS α).Tr s₀ μ s := by
  cases h with
  | stepL htr hrest =>
      cases hrest
      exact htr

/-- Every ID in the final slot, and every ID returned by a read, was either published in
the trace or was already in the initial slot. -/
private theorem slot_or_read_mem {α : Type u} (s₀ : Slot α) (μs : List (Label α))
    (s : Slot α) (h : (registerLTS α).MTr s₀ μs s) :
    (∀ n v, s = some (n, v) → Label.publish n v ∈ μs ∨ s₀ = some (n, v)) ∧
      (∀ n v, Label.read (some (n, v)) ∈ μs → Label.publish n v ∈ μs ∨ s₀ = some (n, v)) := by
  induction h with
  | refl =>
      constructor
      · intro n v hs
        exact Or.inr hs
      · intro n v hr
        simp at hr
  | stepL htr hrest ih =>
      obtain ⟨iha, ihb⟩ := ih
      cases htr with
      | publish pn pv =>
          constructor
          · intro n v hs
            rcases iha n v hs with h | h
            · exact Or.inl (List.mem_cons.mpr (Or.inr h))
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inl List.mem_cons_self
          · intro n v hr
            rcases List.mem_cons.mp hr with h | h
            · cases h
            · rcases ihb n v h with h' | h'
              · exact Or.inl (List.mem_cons.mpr (Or.inr h'))
              · simp only [Option.some.injEq, Prod.mk.injEq] at h'
                obtain ⟨rfl, rfl⟩ := h'
                exact Or.inl List.mem_cons_self
      | read =>
          constructor
          · intro n v hs
            rcases iha n v hs with h | h
            · exact Or.inl (List.mem_cons.mpr (Or.inr h))
            · cases h
          · intro n v hr
            rcases List.mem_cons.mp hr with h | h
            · cases h
              exact Or.inr rfl
            · rcases ihb n v h with h' | h'
              · exact Or.inl (List.mem_cons.mpr (Or.inr h'))
              · cases h'

/-! ### Trace properties -/

/-- Proof-facing: the successful read IDs form a sublist of the publication IDs, for
every finite trace from the empty slot (no monotonicity hypothesis needed). -/
theorem readIds_sublist_publishIds {α : Type u} (μs : List (Label α)) (s : Slot α)
    (h : (registerLTS α).MTr none μs s) :
    (readIds μs).Sublist (publishIds μs) := by
  have hsub := mtr_slot_sublist (none : Slot α) μs s h
  rw [slotIds_none] at hsub
  exact hsub

/-- Successful read IDs inject into publication IDs: an injective map from read positions
to publication positions preserving the ID. -/
theorem exists_injective_readIds_to_publishIds {α : Type u} (μs : List (Label α))
    (s : Slot α) (h : (registerLTS α).MTr none μs s)
    (hinc : (publishIds μs).Pairwise (· < ·)) :
    ∃ f : Fin (readIds μs).length → Fin (publishIds μs).length,
      Function.Injective f ∧ ∀ k, (publishIds μs)[f k] = (readIds μs)[k] := by
  have hsub : (readIds μs).Sublist (publishIds μs) := readIds_sublist_publishIds μs s h
  have hnod : (readIds μs).Nodup :=
    nodup_of_pairwise_lt (List.Pairwise.sublist hsub hinc)
  have hmem : ∀ k : Fin (readIds μs).length, (readIds μs)[k] ∈ publishIds μs := by
    intro k
    exact hsub.subset (List.getElem_mem k.isLt)
  choose g hg hval using fun k => List.mem_iff_getElem.mp (hmem k)
  refine ⟨fun k => ⟨g k, hg k⟩, ?_, ?_⟩
  · intro k₁ k₂ hkk
    have c :=
      congrArg (fun j : Fin (publishIds μs).length => (publishIds μs)[j]) hkk
    have cNat : (publishIds μs)[g k₁]'(hg k₁) = (publishIds μs)[g k₂]'(hg k₂) := c
    rw [hval k₁, hval k₂] at cNat
    have cNat2 : (readIds μs)[k₁.val]'(k₁.isLt) = (readIds μs)[k₂.val]'(k₂.isLt) := cNat
    have hv : k₁.val = k₂.val := (hnod.getElem_inj_iff).mp cNat2
    exact Fin.ext hv
  · intro k
    exact hval k

/-- Successful read IDs are strictly increasing. -/
theorem readIds_pairwise_lt {α : Type u} (μs : List (Label α)) (s : Slot α)
    (h : (registerLTS α).MTr none μs s) (hinc : (publishIds μs).Pairwise (· < ·)) :
    (readIds μs).Pairwise (· < ·) := by
  exact List.Pairwise.sublist (readIds_sublist_publishIds μs s h) hinc

/-- Every publication whose ID is never returned by a read is still pending in the final
slot, or was overwritten by a later publication with no read in between. -/
theorem unreturned_pending_or_overwritten {α : Type u} (μs : List (Label α)) (s : Slot α)
    (h : (registerLTS α).MTr none μs s)
    (i n : ℕ) (v : α) (hi : μs[i]? = some (.publish n v)) (hn : n ∉ readIds μs) :
    s = some (n, v) ∨
      ∃ j, i < j ∧ (∃ m w, μs[j]? = some (.publish m w)) ∧
        ∀ k r, i < k → k < j → μs[k]? ≠ some (.read r) := by
  have hsplit :
      (registerLTS α).MTr none (List.take (i + 1) μs ++ List.drop (i + 1) μs) s := by
    rw [List.take_append_drop]
    exact h
  obtain ⟨s_mid, hpre, hsuf⟩ := mtr_split _ _ hsplit
  have htake : List.take (i + 1) μs = List.take i μs ++ [Label.publish n v] := by
    rw [List.take_add_one, hi, Option.toList_some]
  have hmid : s_mid = some (n, v) := by
    rw [htake] at hpre
    obtain ⟨s_pre, _, hsingle⟩ := mtr_split _ _ hpre
    have htr := mtr_singleton hsingle
    exact (registerLTS_tr_publish_iff _ _ _ _).mp htr
  revert hsuf
  cases hdrop : List.drop (i + 1) μs with
  | nil =>
      intro hsuf
      left
      cases hsuf
      exact hmid
  | cons hd tl =>
      revert hdrop
      cases hd with
      | publish m w =>
          intro hdrop hsuf
          right
          refine ⟨i + 1, by omega, ⟨m, w, ?_⟩, ?_⟩
          · have e := List.getElem?_drop (xs := μs) (i := i + 1) (j := 0)
            rw [hdrop, List.getElem?_cons_zero] at e
            have h10 : i + 1 + 0 = i + 1 := by omega
            rw [h10] at e
            exact e.symm
          · intro k r hik hkj _
            omega
      | read r =>
          intro hdrop hsuf
          cases hsuf with
          | stepL htr _ =>
              have hr := (registerLTS_tr_read_iff _ _ _).mp htr
              rw [hmid] at hr
              have hrr : r = some (n, v) := hr.1
              have e := List.getElem?_drop (xs := μs) (i := i + 1) (j := 0)
              rw [hdrop, List.getElem?_cons_zero] at e
              have h10 : i + 1 + 0 = i + 1 := by omega
              rw [h10, hrr] at e
              have hmem : Label.read (some (n, v)) ∈ μs := List.mem_of_getElem? e.symm
              have hcon : n ∈ readIds μs := by
                simp only [readIds, List.mem_filterMap]
                exact ⟨Label.read (some (n, v)), hmem, rfl⟩
              exact absurd hcon hn

/-- **Overwrite-newest sample register, trace correctness.** For every finite trace from
the empty slot with strictly increasing publication IDs: successful read IDs inject into
publication IDs and are strictly increasing, and each unreturned publication is either
still pending or was overwritten. -/
theorem trace_correct {α : Type u} (μs : List (Label α)) (s : Slot α)
    (h : (registerLTS α).MTr none μs s) (hinc : (publishIds μs).Pairwise (· < ·)) :
    (∃ f : Fin (readIds μs).length → Fin (publishIds μs).length,
        Function.Injective f ∧ ∀ k, (publishIds μs)[f k] = (readIds μs)[k]) ∧
      (readIds μs).Pairwise (· < ·) ∧
      ∀ (i n : ℕ) (v : α), μs[i]? = some (.publish n v) → n ∉ readIds μs →
        s = some (n, v) ∨
          ∃ j, i < j ∧ (∃ m w, μs[j]? = some (.publish m w)) ∧
            ∀ k r, i < k → k < j → μs[k]? ≠ some (.read r) := by
  exact ⟨exists_injective_readIds_to_publishIds μs s h hinc,
    readIds_pairwise_lt μs s h hinc,
    fun i n v hi hn => unreturned_pending_or_overwritten μs s h i n v hi hn⟩

/-- A trace ending in a full slot either kept the initial slot (empty trace) or went
through a last publication of exactly the stored pair, with no publication after it. -/
private theorem last_publish_of_slot_some {α : Type u} {n : ℕ} {v : α}
    (μs : List (Label α)) (s₀ : Slot α) {s : Slot α}
    (h : (registerLTS α).MTr s₀ μs s) (hs : s = some (n, v)) :
    (μs = [] ∧ s₀ = some (n, v)) ∨
      (∃ j, j < μs.length ∧ μs[j]? = some (.publish n v) ∧
        ∀ k m w, j < k → k < μs.length → μs[k]? ≠ some (.publish m w)) := by
  induction μs generalizing s₀ s with
  | nil =>
      cases h
      exact Or.inl ⟨rfl, hs⟩
  | cons mu tl ih =>
      cases h with
      | stepL htr hrest =>
          rcases ih _ hrest hs with ⟨rfl, hs₂⟩ | ⟨j, hj, hpub, hnone⟩
          · cases htr with
            | publish pn pv =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hs₂
                obtain ⟨rfl, rfl⟩ := hs₂
                refine Or.inr ⟨0, by simp, List.getElem?_cons_zero, ?_⟩
                intro k m w h0k hk1 _
                simp only [List.length_cons, List.length_nil] at hk1
                omega
            | read =>
                cases hs₂
          · refine Or.inr ⟨j + 1, ?_, ?_, ?_⟩
            · simp only [List.length_cons]
              omega
            · rw [List.getElem?_cons_succ]
              exact hpub
            · intro k m w hjk hklen hcon
              obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
              rw [List.getElem?_cons_succ] at hcon
              simp only [List.length_cons] at hklen
              exact hnone k' m w (by omega) (by omega) hcon

theorem exists_publish_index_of_read_mem {α : Type u} (μs : List (Label α)) (s : Slot α)
    (h : (registerLTS α).MTr none μs s)
    (i : ℕ) (n : ℕ) (v : α) (hi : μs[i]? = some (.read (some (n, v)))) :
    ∃ j, j < i ∧ μs[j]? = some (.publish n v) ∧
      ∀ k m w, j < k → k < i → μs[k]? ≠ some (.publish m w) := by
  have hsplit :
      (registerLTS α).MTr none (List.take (i + 1) μs ++ List.drop (i + 1) μs) s := by
    rw [List.take_append_drop]
    exact h
  obtain ⟨s_mid, hpre, hsuf⟩ := mtr_split _ _ hsplit
  have htake : List.take (i + 1) μs = List.take i μs ++ [Label.read (some (n, v))] := by
    rw [List.take_add_one, hi, Option.toList_some]
  rw [htake] at hpre
  obtain ⟨s_pre, hpre', hsingle⟩ := mtr_split _ _ hpre
  have htr := mtr_singleton hsingle
  have hr := (registerLTS_tr_read_iff _ _ _).mp htr
  have hsp : s_pre = some (n, v) := hr.1.symm
  rcases last_publish_of_slot_some (List.take i μs) none hpre' hsp with
    ⟨htake_nil, _⟩ | ⟨j, hj, hpub, hnone⟩
  · rw [htake_nil] at hpre'
    cases hpre'
    cases hsp
  · have hji : j < i := by
      rw [List.length_take] at hj
      omega
    refine ⟨j, hji, ?_, ?_⟩
    · rw [← List.getElem?_take_of_lt hji]
      exact hpub
    · intro k m w hjk hki hcon
      have hkl : ¬ μs.length ≤ k := fun hle => by
        rw [List.getElem?_eq_none hle] at hcon
        cases hcon
      have hklen : k < (List.take i μs).length := by
        rw [List.length_take]
        omega
      rw [← List.getElem?_take_of_lt hki] at hcon
      exact hnone k m w hjk hklen hcon

/-- No fabricated values: every successful read returns an `(id, value)` pair that was
published earlier in the trace. -/
theorem publish_mem_of_read_mem {α : Type u} (μs : List (Label α)) (s : Slot α)
    (h : (registerLTS α).MTr none μs s) (n : ℕ) (v : α)
    (hr : Label.read (some (n, v)) ∈ μs) :
    Label.publish n v ∈ μs := by
  obtain ⟨_, ihb⟩ := slot_or_read_mem none μs s h
  rcases ihb n v hr with h' | h'
  · exact h'
  · cases h'

/-! ### Validation -/

/-- Publish twice before a read: the read returns the newer publication and nothing
else. -/
theorem registerLTS_mtr_publish_publish_read_iff {α : Type u} (a b : α)
    (r : Option (ℕ × α)) (s : Slot α) :
    (registerLTS α).MTr none [.publish 0 a, .publish 1 b, .read r] s ↔
      r = some (1, b) ∧ s = none := by
  constructor
  · intro h
    cases h with
    | stepL h1 hr1 =>
        cases h1
        cases hr1 with
        | stepL h2 hr2 =>
            cases h2
            cases hr2 with
            | stepL h3 hr3 =>
                cases h3
                cases hr3
                exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Cslib.LTS.MTr.stepL (RegisterStep.publish _ _ _)
      (Cslib.LTS.MTr.stepL (RegisterStep.publish _ _ _)
        (Cslib.LTS.MTr.stepL (RegisterStep.read _) Cslib.LTS.MTr.refl))

/-- Publish twice before a read loses exactly the older ID. -/
theorem readIds_publish_publish_read {α : Type u} (a b : α) :
    readIds [Label.publish 0 a, .publish 1 b, .read (some (1, b))] = [1] ∧
      publishIds [Label.publish 0 a, .publish 1 b, .read (some (1, b))] = [0, 1] := by
  exact ⟨rfl, rfl⟩

/-- Double read: the first read returns the value, the second returns `none`. -/
theorem registerLTS_mtr_publish_read_read_iff {α : Type u} (n : ℕ) (v : α)
    (r1 r2 : Option (ℕ × α)) (s : Slot α) :
    (registerLTS α).MTr none [.publish n v, .read r1, .read r2] s ↔
      r1 = some (n, v) ∧ r2 = none ∧ s = none := by
  constructor
  · intro h
    cases h with
    | stepL h1 hr1 =>
        cases h1
        cases hr1 with
        | stepL h2 hr2 =>
            cases h2
            cases hr2 with
            | stepL h3 hr3 =>
                cases h3
                cases hr3
                exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact Cslib.LTS.MTr.stepL (RegisterStep.publish _ _ _)
      (Cslib.LTS.MTr.stepL (RegisterStep.read _)
        (Cslib.LTS.MTr.stepL (RegisterStep.read _) Cslib.LTS.MTr.refl))

/-- A read of the empty register returns `none`: no value is fabricated. -/
theorem registerLTS_mtr_read_empty_iff {α : Type u} (r : Option (ℕ × α)) (s : Slot α) :
    (registerLTS α).MTr none [.read r] s ↔ r = none ∧ s = none := by
  constructor
  · intro h
    cases h with
    | stepL h1 hr1 =>
        cases h1
        cases hr1
        exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Cslib.LTS.MTr.stepL (RegisterStep.read _) Cslib.LTS.MTr.refl

/-- Violated premise: with publication IDs `1` then `0`, the trace is valid but the read IDs
`[1, 0]` are not strictly increasing. -/
theorem readIds_not_pairwise_of_decreasing_publish {α : Type u} (a b : α) :
    (registerLTS α).MTr none
        [.publish 1 a, .read (some (1, a)), .publish 0 b, .read (some (0, b))] none ∧
      ¬ (readIds [Label.publish 1 a, .read (some (1, a)), .publish 0 b,
          .read (some (0, b))]).Pairwise (· < ·) := by
  refine ⟨?_, ?_⟩
  · exact Cslib.LTS.MTr.stepL (RegisterStep.publish _ _ _)
      (Cslib.LTS.MTr.stepL (RegisterStep.read _)
        (Cslib.LTS.MTr.stepL (RegisterStep.publish _ _ _)
          (Cslib.LTS.MTr.stepL (RegisterStep.read _) Cslib.LTS.MTr.refl)))
  · show ¬ ([1, 0] : List ℕ).Pairwise (· < ·)
    intro hcon
    have h1 := (List.pairwise_cons.mp hcon).1 0 List.mem_cons_self
    omega

end Cslib.Semantics.Peripheral.OverwriteSampleRegister
