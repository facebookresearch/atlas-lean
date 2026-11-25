/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.OverwriteSampleRegister
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Fintype.Card

/-!
# Sample-ready protocol

A driver for the overwrite-sample register: it polls the Ready
observation of the current slot, then performs an atomic optional
read. Ready is a pure observation of the register slot, not a
second register. Publications and reads by other permitted readers
may interleave between the poll and the read, so the read may
return `none`; the driver handles that case explicitly with a
retry and never delivers `none` as a sample. Every delivered
sample is the result of the driver's latest read, with only
environment steps in between, and carries the publication ID of
the publication the slot actually held when it was read.
-/

@[expose] public section

universe u v

namespace Cslib.Semantics.Peripheral.SampleReadyProtocol

open Cslib.Semantics.Peripheral.OverwriteSampleRegister

/-- The Ready observation of the register: the slot is nonempty. -/
def ready {α : Type u} (s : Slot α) : Bool :=
  s.isSome

/-- Driver control state: about to poll, polled with the observed Ready bit, or holding the
result of its atomic optional read (its only local data). -/
inductive Phase (α : Type u) : Type u where
  | idle
  | polled (ready : Bool)
  | fetched (result : Option (ℕ × α))

/-- Labels of the closed driver/register system: an environment register step (publication or
another permitted read), a Ready poll, the driver's atomic optional read, delivery of a sample to
the consumer, or a retry. -/
inductive DriverLabel (α : Type u) : Type u where
  | env (μ : Label α)
  | poll (ready : Bool)
  | read (result : Option (ℕ × α))
  | deliver (id : ℕ) (value : α)
  | retry

/-- Transitions of the closed system. Environment steps are L1 register steps at any driver
phase; the driver polls Ready of the current slot, reads (an L1 read) only after observing
Ready = `true`, delivers only a fetched `some` result, and retries on Ready = `false` or on an
empty read. -/
inductive DriverStep {α : Type u} : Phase α × Slot α → DriverLabel α → Phase α × Slot α → Prop
  where
  | env (p : Phase α) {s s' : Slot α} {μ : Label α} (h : RegisterStep s μ s') :
      DriverStep (p, s) (.env μ) (p, s')
  | poll (s : Slot α) : DriverStep (.idle, s) (.poll (ready s)) (.polled (ready s), s)
  | read {s s' : Slot α} {r : Option (ℕ × α)} (h : RegisterStep s (.read r) s') :
      DriverStep (.polled true, s) (.read r) (.fetched r, s')
  | deliver (n : ℕ) (v : α) (s : Slot α) :
      DriverStep (.fetched (some (n, v)), s) (.deliver n v) (.idle, s)
  | retryNotReady (s : Slot α) : DriverStep (.polled false, s) .retry (.idle, s)
  | retryEmpty (s : Slot α) : DriverStep (.fetched none, s) .retry (.idle, s)

/-- The closed driver/register system as a `Cslib.LTS`. -/
def driverLTS (α : Type u) : Cslib.LTS (Phase α × Slot α) (DriverLabel α) where
  Tr := DriverStep

/-- The register operation performed by a closed-system step, if any: environment steps and
the driver's read are L1 register steps; poll, deliver and retry touch no register state. -/
def registerLabel? {α : Type u} : DriverLabel α → Option (Label α)
  | .env μ => some μ
  | .read r => some (.read r)
  | _ => none

/-- IDs of the samples delivered in a trace, in order. -/
def deliveredIds {α : Type u} (μs : List (DriverLabel α)) : List ℕ :=
  μs.filterMap fun
    | .deliver n _ => some n
    | _ => none

/-! ### The two driver operations -/

/-- **Ready observes nonemptiness.** -/
theorem ready_eq_true_iff {α : Type u} (s : Slot α) :
    ready s = true ↔ ∃ n v, s = some (n, v) := by
  cases s with
  | none => simp [ready]
  | some p => obtain ⟨n, v⟩ := p; simp [ready]

/-- **Ready reads the same slot.** A poll is enabled exactly from `idle`, observes Ready of the
current slot, and leaves the slot unchanged. -/
theorem driverLTS_tr_poll_iff {α : Type u} (x x' : Phase α × Slot α) (b : Bool) :
    (driverLTS α).Tr x (.poll b) x' ↔
      ∃ s, x = (.idle, s) ∧ b = ready s ∧ x' = (.polled b, s) := by
  constructor
  · intro h
    cases h with
    | poll s => exact ⟨s, rfl, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl, rfl⟩
    exact DriverStep.poll s

/-- **Atomic optional read.** The driver's read is enabled exactly after observing
Ready = `true`; as an L1 read it returns the whole current slot (possibly `none`) and clears it. -/
theorem driverLTS_tr_read_iff {α : Type u} (x x' : Phase α × Slot α) (r : Option (ℕ × α)) :
    (driverLTS α).Tr x (.read r) x' ↔
      ∃ s, x = (.polled true, s) ∧ r = s ∧ x' = (.fetched r, none) := by
  constructor
  · intro h
    cases h with
    | read hr => cases hr; exact ⟨_, rfl, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl, rfl⟩
    exact DriverStep.read (RegisterStep.read _)

/-! ### Trace properties -/

/-- **The closed system runs on the L1 register.** Every finite closed-system trace projects,
by keeping the environment steps and the driver's reads, to an L1 register trace between the
same slots. -/
theorem registerLTS_mtr_filterMap_of_driverLTS_mtr {α : Type u} (p p' : Phase α)
    (s₀ s : Slot α) (μs : List (DriverLabel α)) (h : (driverLTS α).MTr (p, s₀) μs (p', s)) :
    (registerLTS α).MTr s₀ (μs.filterMap registerLabel?) s := by
  generalize hx : ((p, s₀) : Phase α × Slot α) = x at h
  generalize hy : ((p', s) : Phase α × Slot α) = y at h
  induction h generalizing p s₀ with
  | refl => cases hx; cases hy; exact Cslib.LTS.MTr.refl
  | @stepL x1 μ x2 μs x3 htr hrest ih =>
      subst hx hy
      obtain ⟨q, t⟩ := x2
      have ih' := ih q t rfl rfl
      cases htr with
      | env _ hr => exact Cslib.LTS.MTr.stepL hr ih'
      | poll => exact ih'
      | read hr => exact Cslib.LTS.MTr.stepL hr ih'
      | deliver => exact ih'
      | retryNotReady => exact ih'
      | retryEmpty => exact ih'

private theorem exists_read_some_aux {α : Type u} (y x : Phase α × Slot α)
    (μs : List (DriverLabel α)) (h : (driverLTS α).MTr y μs x) :
    ∀ (i n : ℕ) (v : α), μs[i]? = some (.deliver n v) →
      (∃ j, j < i ∧ μs[j]? = some (.read (some (n, v))) ∧
        ∀ k, j < k → k < i → ∃ μ, μs[k]? = some (.env μ)) ∨
      (y.1 = .fetched (some (n, v)) ∧ ∀ k, k < i → ∃ μ, μs[k]? = some (.env μ)) := by
  induction h with
  | refl => intro i n v hi; simp at hi
  | @stepL x1 μ x2 μs x3 htr hrest ih =>
      intro i n v hi
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          have hμ : μ = .deliver n v := by simpa using hi
          subst hμ
          cases htr with
          | deliver n' v' s =>
              right
              refine ⟨rfl, ?_⟩
              intro k hk
              omega
      | succ i' =>
          rw [List.getElem?_cons_succ] at hi
          rcases ih i' n v hi with ⟨j, hj, hread, henv⟩ | ⟨hmid, henv⟩
          · left
            refine ⟨j + 1, by omega, ?_, ?_⟩
            · rwa [List.getElem?_cons_succ]
            · intro k hjk hki
              cases k with
              | zero => omega
              | succ k' =>
                  rw [List.getElem?_cons_succ]
                  exact henv k' (by omega) (by omega)
          · cases htr with
            | env p hr =>
                right
                refine ⟨hmid, ?_⟩
                intro k hk
                cases k with
                | zero =>
                    rw [List.getElem?_cons_zero]
                    exact ⟨_, rfl⟩
                | succ k' =>
                    rw [List.getElem?_cons_succ]
                    exact henv k' (by omega)
            | poll s => cases hmid
            | read hr =>
                cases hr
                left
                refine ⟨0, by omega, ?_, ?_⟩
                · rw [List.getElem?_cons_zero]
                  simpa using hmid
                · intro k hjk hki
                  cases k with
                  | zero => omega
                  | succ k' =>
                      rw [List.getElem?_cons_succ]
                      exact henv k' (by omega)
            | deliver n' v' s => cases hmid
            | retryNotReady s => cases hmid
            | retryEmpty s => cases hmid

/-- **No `none` is delivered.** In every finite trace from an idle driver and an empty slot,
under arbitrary interleaving of publications and other reads, each delivered sample `(n, v)` is
the result `some (n, v)` of the driver's latest read, with only environment steps in between. -/
theorem exists_read_some_of_deliver {α : Type u} (μs : List (DriverLabel α))
    (x : Phase α × Slot α) (h : (driverLTS α).MTr (.idle, none) μs x) (i n : ℕ) (v : α)
    (hi : μs[i]? = some (.deliver n v)) :
    ∃ j, j < i ∧ μs[j]? = some (.read (some (n, v))) ∧
      ∀ k, j < k → k < i → ∃ μ, μs[k]? = some (.env μ) := by
  rcases exists_read_some_aux (.idle, none) x μs h i n v hi with hres | ⟨hmid, -⟩
  · exact hres
  · cases hmid

private theorem first_nonenv_after_fetched_none {α : Type u} (y x : Phase α × Slot α)
    (μs : List (DriverLabel α)) (h : (driverLTS α).MTr y μs x) :
    y.1 = .fetched none →
    ∀ (t : ℕ) (ℓ : DriverLabel α), (∀ l, l < t → ∃ μ, μs[l]? = some (.env μ)) →
      μs[t]? = some ℓ → (∀ μ, ℓ ≠ .env μ) → ℓ = .retry := by
  induction h with
  | refl => intro _ t ℓ _ ht _; simp at ht
  | @stepL x1 μ x2 μs x3 htr hrest ih =>
      intro hy t ℓ henv ht hnonenv
      cases t with
      | zero =>
          rw [List.getElem?_cons_zero] at ht
          have hμ : μ = ℓ := by simpa using ht
          subst hμ
          cases htr with
          | env p hr => exact (hnonenv _ rfl).elim
          | poll s => cases hy
          | read hr => cases hy
          | deliver n' v' s => cases hy
          | retryNotReady s => cases hy
          | retryEmpty s => rfl
      | succ t' =>
          obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, μ = .env μ₀ := by
            have h0 := henv 0 (by omega)
            rw [List.getElem?_cons_zero] at h0
            obtain ⟨μ₀, hμ₀⟩ := h0
            exact ⟨μ₀, by simpa using hμ₀⟩
          subst hμ₀
          cases htr with
          | env p hr =>
              refine ih hy t' ℓ ?_ ?_ hnonenv
              · intro l hl
                have h1 := henv (l + 1) (by omega)
                rwa [List.getElem?_cons_succ] at h1
              · rwa [List.getElem?_cons_succ] at ht

private theorem retry_aux {α : Type u} (y x : Phase α × Slot α)
    (μs : List (DriverLabel α)) (h : (driverLTS α).MTr y μs x) :
    ∀ (j k : ℕ), μs[j]? = some (.read none) → j < k →
      (∀ l, j < l → l < k → ∃ μ, μs[l]? = some (.env μ)) →
      (∃ ℓ, μs[k]? = some ℓ ∧ ∀ μ, ℓ ≠ .env μ) → μs[k]? = some .retry := by
  induction h with
  | refl => intro j k hj; simp at hj
  | @stepL x1 μ x2 μs x3 htr hrest ih =>
      intro j k hj hjk henv hk
      cases j with
      | zero =>
          rw [List.getElem?_cons_zero] at hj
          have hμ : μ = .read none := by simpa using hj
          subst hμ
          cases htr with
          | read hr =>
              cases hr
              cases k with
              | zero => exact (Nat.not_lt_zero _ hjk).elim
              | succ k' =>
                  obtain ⟨ℓ, hℓ, hnonenv⟩ := hk
                  rw [List.getElem?_cons_succ] at hℓ
                  have hres := first_nonenv_after_fetched_none _ _ _ hrest rfl k' ℓ
                    (by
                      intro l hl
                      have h1 := henv (l + 1) (by omega) (by omega)
                      rwa [List.getElem?_cons_succ] at h1) hℓ hnonenv
                  rw [hres] at hℓ
                  rwa [List.getElem?_cons_succ]
      | succ j' =>
          cases k with
          | zero => exact (Nat.not_lt_zero _ hjk).elim
          | succ k' =>
              rw [List.getElem?_cons_succ] at hj
              obtain ⟨ℓ, hℓ, hnonenv⟩ := hk
              rw [List.getElem?_cons_succ] at hℓ
              have hres := ih j' k' hj (by omega)
                (by
                  intro l hl1 hl2
                  have h1 := henv (l + 1) (by omega) (by omega)
                  rwa [List.getElem?_cons_succ] at h1) ⟨ℓ, hℓ, hnonenv⟩
              rw [List.getElem?_cons_succ]
              exact hres

/-- **The empty read is handled explicitly.** After a driver read that returned `none`, the
next driver (non-environment) step in the trace is `retry`. -/
theorem retry_of_read_none {α : Type u} (μs : List (DriverLabel α)) (x : Phase α × Slot α)
    (h : (driverLTS α).MTr (.idle, none) μs x) (j k : ℕ) (hj : μs[j]? = some (.read none))
    (hjk : j < k) (henv : ∀ l, j < l → l < k → ∃ μ, μs[l]? = some (.env μ))
    (hk : ∃ ℓ, μs[k]? = some ℓ ∧ ∀ μ, ℓ ≠ .env μ) :
    μs[k]? = some .retry := by
  exact retry_aux (.idle, none) x μs h j k hj hjk henv hk

private theorem exists_publish_before_read_aux {α : Type u} (y x : Phase α × Slot α)
    (μs : List (DriverLabel α)) (h : (driverLTS α).MTr y μs x) :
    ∀ (j n : ℕ) (v : α), μs[j]? = some (.read (some (n, v))) →
      (∃ k, k < j ∧ μs[k]? = some (.env (.publish n v)) ∧
        ∀ l m w, k < l → l < j → μs[l]? ≠ some (.env (.publish m w))) ∨
      (y.2 = some (n, v) ∧ ∀ l m w, l < j → μs[l]? ≠ some (.env (.publish m w))) := by
  induction h with
  | refl => intro j n v hj; simp at hj
  | @stepL x1 μ x2 μs x3 htr hrest ih =>
      intro j n v hj
      cases j with
      | zero =>
          rw [List.getElem?_cons_zero] at hj
          have hμ : μ = .read (some (n, v)) := by simpa using hj
          subst hμ
          cases htr with
          | read hr =>
              cases hr
              right
              refine ⟨rfl, ?_⟩
              intro l m w hl
              exact (Nat.not_lt_zero _ hl).elim
      | succ j' =>
          rw [List.getElem?_cons_succ] at hj
          rcases ih j' n v hj with ⟨k, hk, hpub, hnopub⟩ | ⟨hmid, hnopub⟩
          · left
            refine ⟨k + 1, by omega, ?_, ?_⟩
            · rwa [List.getElem?_cons_succ]
            · intro l m w hl1 hl2 hcon
              cases l with
              | zero => exact (Nat.not_lt_zero _ hl1).elim
              | succ l' =>
                  rw [List.getElem?_cons_succ] at hcon
                  exact hnopub l' m w (by omega) (by omega) hcon
          · cases htr with
            | env p hr =>
                cases hr with
                | publish m w =>
                    left
                    refine ⟨0, by omega, ?_, ?_⟩
                    · rw [List.getElem?_cons_zero]
                      simpa using hmid
                    · intro l m' w' hl1 hl2 hcon
                      cases l with
                      | zero => exact (lt_irrefl _ hl1).elim
                      | succ l' =>
                          rw [List.getElem?_cons_succ] at hcon
                          exact hnopub l' m' w' (by omega) hcon
                | read => simp at hmid
            | poll s =>
                right
                refine ⟨hmid, ?_⟩
                intro l m w hl hcon
                cases l with
                | zero =>
                    rw [List.getElem?_cons_zero] at hcon
                    simp at hcon
                | succ l' =>
                    rw [List.getElem?_cons_succ] at hcon
                    exact hnopub l' m w (by omega) hcon
            | read hr =>
                cases hr
                simp at hmid
            | deliver n' v' s =>
                right
                refine ⟨hmid, ?_⟩
                intro l m w hl hcon
                cases l with
                | zero =>
                    rw [List.getElem?_cons_zero] at hcon
                    simp at hcon
                | succ l' =>
                    rw [List.getElem?_cons_succ] at hcon
                    exact hnopub l' m w (by omega) hcon
            | retryNotReady s =>
                right
                refine ⟨hmid, ?_⟩
                intro l m w hl hcon
                cases l with
                | zero =>
                    rw [List.getElem?_cons_zero] at hcon
                    simp at hcon
                | succ l' =>
                    rw [List.getElem?_cons_succ] at hcon
                    exact hnopub l' m w (by omega) hcon
            | retryEmpty s =>
                right
                refine ⟨hmid, ?_⟩
                intro l m w hl hcon
                cases l with
                | zero =>
                    rw [List.getElem?_cons_zero] at hcon
                    simp at hcon
                | succ l' =>
                    rw [List.getElem?_cons_succ] at hcon
                    exact hnopub l' m w (by omega) hcon

/-- **Every delivered sample carries its actual publication ID.** In every finite trace from an
idle driver and an empty slot, each delivered `(n, v)` was fed by a driver read at `j` that is
preceded by the publication `publish n v` at `k`, with no other publication between `k` and `j`:
the value and ID the slot actually held when it was read. -/
theorem exists_publish_of_deliver {α : Type u} (μs : List (DriverLabel α))
    (x : Phase α × Slot α) (h : (driverLTS α).MTr (.idle, none) μs x) (i n : ℕ) (v : α)
    (hi : μs[i]? = some (.deliver n v)) :
    ∃ j k, k < j ∧ j < i ∧ μs[j]? = some (.read (some (n, v))) ∧
      μs[k]? = some (.env (.publish n v)) ∧
      ∀ l m w, k < l → l < j → μs[l]? ≠ some (.env (.publish m w)) := by
  obtain ⟨j, hj, hread, -⟩ := exists_read_some_of_deliver μs x h i n v hi
  rcases exists_publish_before_read_aux (.idle, none) x μs h j n v hread with
    ⟨k, hk, hpub, hnopub⟩ | ⟨hmid, -⟩
  · exact ⟨j, k, hk, hj, hread, hpub, hnopub⟩
  · simp at hmid

/-- **Ready-then-read driver correctness (headline).** In every finite trace from an idle driver
and an empty slot, with publications and other permitted reads interleaved arbitrarily, every
delivered sample `(n, v)` (1) is the `some (n, v)` result of the driver's latest read, with only
environment steps between that read and the delivery, so `none` is never delivered, and (2)
carries its actual publication ID: that read is preceded by `publish n v` with no other
publication in between. -/
theorem deliver_correct {α : Type u} (μs : List (DriverLabel α)) (x : Phase α × Slot α)
    (h : (driverLTS α).MTr (.idle, none) μs x) (i n : ℕ) (v : α)
    (hi : μs[i]? = some (.deliver n v)) :
    ∃ j k, k < j ∧ j < i ∧ μs[j]? = some (.read (some (n, v))) ∧
      (∀ l, j < l → l < i → ∃ μ, μs[l]? = some (.env μ)) ∧
      μs[k]? = some (.env (.publish n v)) ∧
      ∀ l m w, k < l → l < j → μs[l]? ≠ some (.env (.publish m w)) := by
  obtain ⟨j, hj, hread, henv⟩ := exists_read_some_of_deliver μs x h i n v hi
  rcases exists_publish_before_read_aux (.idle, none) x μs h j n v hread with
    ⟨k, hk, hpub, hnopub⟩ | ⟨hmid, -⟩
  · exact ⟨j, k, hk, hj, hread, henv, hpub, hnopub⟩
  · simp at hmid

private def fetchedId? {α : Type u} : Phase α → List ℕ
  | .fetched (some (n, _)) => [n]
  | _ => []

private def slotId? {α : Type u} : Slot α → List ℕ
  | some (n, _) => [n]
  | none => []

private def pendingIds {α : Type u} (p : Phase α) (s : Slot α) : List ℕ :=
  fetchedId? p ++ slotId? s

private theorem fetchedId?_eq_slotId? {α : Type u} (r : Option (ℕ × α)) :
    fetchedId? (.fetched r) = slotId? r := by
  cases r with
  | none => rfl
  | some p => obtain ⟨n, v⟩ := p; rfl

private theorem deliveredIds_sublist_aux {α : Type u} (y x : Phase α × Slot α)
    (μs : List (DriverLabel α)) (h : (driverLTS α).MTr y μs x) :
    (deliveredIds μs).Sublist
      (pendingIds y.1 y.2 ++ publishIds (μs.filterMap registerLabel?)) := by
  induction h with
  | refl => exact List.nil_sublist _
  | @stepL x1 μ x2 μs x3 htr hrest ih =>
      cases htr with
      | env p hr =>
          cases hr with
          | publish m w =>
              simp only [deliveredIds, publishIds, pendingIds, fetchedId?, slotId?,
                List.filterMap_cons, registerLabel?] at ih ⊢
              refine ih.trans ?_
              simp only [List.append_assoc]
              exact List.Sublist.append (List.Sublist.refl _)
                (List.sublist_append_right _ _)
          | read =>
              simp only [deliveredIds, publishIds, pendingIds, fetchedId?, slotId?,
                List.filterMap_cons, registerLabel?] at ih ⊢
              refine ih.trans ?_
              simp only [List.append_assoc, List.append_nil]
              exact List.Sublist.append (List.Sublist.refl _)
                (List.sublist_append_right _ _)
      | poll s =>
          simp only [deliveredIds, publishIds, pendingIds, fetchedId?, slotId?,
            List.filterMap_cons, registerLabel?] at ih ⊢
          exact ih
      | read hr =>
          cases hr
          simp only [pendingIds] at ih
          rw [fetchedId?_eq_slotId?] at ih
          simp only [deliveredIds, publishIds, pendingIds, fetchedId?, slotId?,
            List.filterMap_cons, registerLabel?, List.append_nil, List.nil_append] at ih ⊢
          exact ih
      | deliver n v s =>
          simp only [deliveredIds, publishIds, pendingIds, fetchedId?, slotId?,
            List.filterMap_cons, registerLabel?] at ih ⊢
          exact List.Sublist.cons_cons _ ih
      | retryNotReady s =>
          simp only [deliveredIds, publishIds, pendingIds, fetchedId?, slotId?,
            List.filterMap_cons, registerLabel?] at ih ⊢
          exact ih
      | retryEmpty s =>
          simp only [deliveredIds, publishIds, pendingIds, fetchedId?, slotId?,
            List.filterMap_cons, registerLabel?] at ih ⊢
          exact ih

/-- **Delivered IDs are strictly increasing.** If the publication IDs of the projected register
trace are strictly increasing, so are the IDs of the delivered samples. -/
theorem deliveredIds_pairwise_lt {α : Type u} (μs : List (DriverLabel α))
    (x : Phase α × Slot α) (h : (driverLTS α).MTr (.idle, none) μs x)
    (hinc : (publishIds (μs.filterMap registerLabel?)).Pairwise (· < ·)) :
    (deliveredIds μs).Pairwise (· < ·) := by
  have hsub := deliveredIds_sublist_aux (.idle, none) x μs h
  simp only [pendingIds, fetchedId?, slotId?, List.nil_append, List.append_nil] at hsub
  exact List.Pairwise.sublist hsub hinc

/-! ### Validation -/

/-- **Publish between Ready and Read.** After `publish 0 a`, a poll, then `publish 1 c`, the
driver's read returns the newer `(1, c)` and that is the only sample it can deliver. -/
theorem driverLTS_mtr_publish_between_poll_and_read_iff {α : Type u} (a c : α) (b : Bool)
    (r : Option (ℕ × α)) (n : ℕ) (w : α) (x : Phase α × Slot α) :
    (driverLTS α).MTr (.idle, none)
        [.env (.publish 0 a), .poll b, .env (.publish 1 c), .read r, .deliver n w] x ↔
      b = true ∧ r = some (1, c) ∧ n = 1 ∧ w = c ∧ x = (.idle, none) := by
  constructor
  · intro h
    cases h with | stepL h1 r1 =>
    cases h1 with | env _ h1 =>
    cases h1
    cases r1 with | stepL h2 r2 =>
    cases h2
    cases r2 with | stepL h3 r3 =>
    cases h3 with | env _ h3 =>
    cases h3
    cases r3 with | stepL h4 r4 =>
    cases h4 with | read h4 =>
    cases h4
    cases r4 with | stepL h5 r5 =>
    cases h5
    cases r5
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact .stepL (.env _ (.publish _ _ _)) (.stepL (.poll _) (.stepL (.env _ (.publish _ _ _))
      (.stepL (.read (.read _)) (.stepL (.deliver _ _ _) .refl))))

/-- **An interleaving clear makes the read empty; Ready is not a latch.** After `publish 0 a`
and a poll, another permitted read clears the slot; the driver had observed Ready = `true`, its
read returns `none`, and it retries. -/
theorem driverLTS_mtr_clear_between_poll_and_read_iff {α : Type u} (a : α) (b : Bool)
    (r₀ r : Option (ℕ × α)) (x : Phase α × Slot α) :
    (driverLTS α).MTr (.idle, none)
        [.env (.publish 0 a), .poll b, .env (.read r₀), .read r, .retry] x ↔
      b = true ∧ r₀ = some (0, a) ∧ r = none ∧ x = (.idle, none) := by
  constructor
  · intro h
    cases h with | stepL h1 r1 =>
    cases h1 with | env _ h1 =>
    cases h1
    cases r1 with | stepL h2 r2 =>
    cases h2
    cases r2 with | stepL h3 r3 =>
    cases h3 with | env _ h3 =>
    cases h3
    cases r3 with | stepL h4 r4 =>
    cases h4 with | read h4 =>
    cases h4
    cases r4 with | stepL h5 r5 =>
    cases h5
    cases r5
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact .stepL (.env _ (.publish _ _ _)) (.stepL (.poll _) (.stepL (.env _ (.read _))
      (.stepL (.read (.read _)) (.stepL (.retryEmpty _) .refl))))

/-- **No stale local data.** After delivering `(0, a)`, a second round with Ready = `true` whose
slot is cleared by another reader before the driver's read cannot deliver anything, in
particular not the stale `(0, a)`. -/
theorem not_driverLTS_mtr_deliver_after_clear {α : Type u} (a c : α) (r : Option (ℕ × α))
    (n : ℕ) (w : α) (x : Phase α × Slot α) :
    ¬ (driverLTS α).MTr (.idle, none)
        [.env (.publish 0 a), .poll true, .read (some (0, a)), .deliver 0 a,
          .env (.publish 1 c), .poll true, .env (.read (some (1, c))), .read r, .deliver n w] x := by
  intro h
  cases h with | stepL h1 r1 =>
  cases h1 with | env _ h1 =>
  cases h1
  cases r1 with | stepL h2 r2 =>
  cases h2
  cases r2 with | stepL h3 r3 =>
  cases h3 with | read h3 =>
  cases h3
  cases r3 with | stepL h4 r4 =>
  cases h4
  cases r4 with | stepL h5 r5 =>
  cases h5 with | env _ h5 =>
  cases h5
  cases r5 with | stepL h6 r6 =>
  cases h6
  cases r6 with | stepL h7 r7 =>
  cases h7 with | env _ h7 =>
  cases h7
  cases r7 with | stepL h8 r8 =>
  cases h8 with | read h8 =>
  cases h8
  cases r8 with | stepL h9 r9 =>
  cases h9

/-- **Violated premise: decreasing publication IDs.** With publications `1` then `0`, the trace
is valid and delivers both samples, but the delivered IDs `[1, 0]` are not strictly
increasing. -/
theorem deliveredIds_not_pairwise_of_decreasing_publish {α : Type u} (a c : α) :
    (driverLTS α).MTr (.idle, none)
        [.env (.publish 1 a), .poll true, .read (some (1, a)), .deliver 1 a,
          .env (.publish 0 c), .poll true, .read (some (0, c)), .deliver 0 c] (.idle, none) ∧
      ¬ (deliveredIds [DriverLabel.env (.publish 1 a), .poll true, .read (some (1, a)),
          .deliver 1 a, .env (.publish 0 c), .poll true, .read (some (0, c)),
          .deliver 0 c]).Pairwise (· < ·) := by
  refine ⟨?_, ?_⟩
  · exact .stepL (.env _ (.publish _ _ _)) (.stepL (.poll _) (.stepL (.read (.read _))
      (.stepL (.deliver _ _ _) (.stepL (.env _ (.publish _ _ _)) (.stepL (.poll _)
        (.stepL (.read (.read _)) (.stepL (.deliver _ _ _) .refl)))))))
  · show ¬ ([1, 0] : List ℕ).Pairwise (· < ·)
    intro hcon
    have h1 := (List.pairwise_cons.mp hcon).1 0 List.mem_cons_self
    omega

end Cslib.Semantics.Peripheral.SampleReadyProtocol
