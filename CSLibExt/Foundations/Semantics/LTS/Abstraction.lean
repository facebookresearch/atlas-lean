/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Simulation

/-!
# Existential abstraction for labelled transition systems

Given an abstraction map `α : S → T`, the existential (direct-image)
abstraction `existsAbs` of an LTS over `S` is the LTS over `T` whose
transitions join every pair of concrete representatives. The graph of `α` is
a simulation into the abstraction, so executions and reachability map
forward, abstract safety implies concrete safety, and abstract paths can be
tested for feasibility with the constrained-reachability sets.

Abstract safety conclusions here are safety (reachability) only: no liveness
and no ACTL* or CEGAR claim.
-/

@[expose] public section

namespace Cslib

namespace LTS

/-- Existential (direct-image) abstraction of an LTS along `α : S → T`: the
abstract transition relation holds at `a μ b` iff some concrete transition
`s -μ→ t` has `α s = a` and `α t = b`. Abstract safety conclusions are
safety (reachability) only: no liveness and no ACTL* or CEGAR claim. -/
def existsAbs {S T Label : Type*} (lts : LTS S Label) (α : S → T) :
    LTS T Label where
  Tr := fun a μ b => ∃ s t, α s = a ∧ α t = b ∧ lts.Tr s μ t

/-- Characterisation of the abstract transition relation, unfolding
`existsAbs`. Abstract safety conclusions are safety (reachability) only: no
liveness and no ACTL* or CEGAR claim. -/
theorem existsAbs_tr_iff {S T Label : Type*} (lts : LTS S Label) (α : S → T)
    (a : T) (μ : Label) (b : T) :
    (existsAbs lts α).Tr a μ b ↔
      ∃ s t, α s = a ∧ α t = b ∧ lts.Tr s μ t :=
  Iff.rfl

/-- The graph of `α` is a simulation from an LTS into its existential
abstraction. Abstract safety conclusions are safety (reachability) only: no
liveness and no ACTL* or CEGAR claim. -/
theorem isSimulation_existsAbs {S T Label : Type*} (lts : LTS S Label)
    (α : S → T) :
    IsSimulation lts (existsAbs lts α) (fun s a => α s = a) := by
  intro s a h μ s' htr
  exact ⟨α s', ⟨s, s', h, rfl, htr⟩, rfl⟩

/-- Executions map forward into the existential abstraction along the same
label list. Abstract safety conclusions are safety (reachability) only: no
liveness and no ACTL* or CEGAR claim. -/
theorem existsAbs_mtr {S T Label : Type*} (lts : LTS S Label) (α : S → T)
    {s : S} {μs : List Label} {t : S} :
    lts.MTr s μs t → (existsAbs lts α).MTr (α s) μs (α t) := by
  intro h
  obtain ⟨_, hm, rfl⟩ :=
    IsSimulation.sim_trace (isSimulation_existsAbs lts α) rfl _ _ h
  exact hm

/-- Reachability maps forward into the existential abstraction. Abstract
safety conclusions are safety (reachability) only: no liveness and no ACTL*
or CEGAR claim. -/
theorem existsAbs_canReach {S T Label : Type*} (lts : LTS S Label)
    (α : S → T) {s t : S} :
    lts.CanReach s t → (existsAbs lts α).CanReach (α s) (α t) := by
  intro h
  obtain ⟨μs, hm⟩ := h
  exact ⟨μs, existsAbs_mtr lts α hm⟩

/-- Safety transfer through the existential abstraction: if every abstract
state reachable from an abstracted initial state lies outside the `α`-image
of `Bad`, then no `Bad` state is reachable from `Init`. This is a safety
(reachability) conclusion only: no liveness and no ACTL* or CEGAR claim. -/
theorem safe_of_existsAbs {S T Label : Type*} (lts : LTS S Label) (α : S → T)
    (Init Bad : S → Prop)
    (hSafe : ∀ a : T,
      (∃ s₀, Init s₀ ∧ (existsAbs lts α).CanReach (α s₀) a) →
      ¬ ∃ s, Bad s ∧ α s = a) :
    ∀ s₀ t, Init s₀ → lts.CanReach s₀ t → ¬ Bad t := by
  intro s₀ t hInit hReach hBad
  have hAbs : (existsAbs lts α).CanReach (α s₀) (α t) :=
    existsAbs_canReach lts α hReach
  exact (hSafe (α t) ⟨s₀, hInit, hAbs⟩) ⟨t, hBad, rfl⟩

/-- Safety transfer with overapproximating abstract initial and bad sets: if
`InitAbs` and `BadAbs` cover the `α`-images of `Init` and `Bad` and the
abstract system is safe, then so is the concrete one. This is a safety
(reachability) conclusion only: no liveness and no ACTL* or CEGAR claim. -/
theorem safe_of_existsAbs_over {S T Label : Type*} (lts : LTS S Label)
    (α : S → T) (Init Bad : S → Prop) (InitAbs BadAbs : T → Prop)
    (hInit : ∀ s, Init s → InitAbs (α s))
    (hBad : ∀ s, Bad s → BadAbs (α s))
    (hSafe : ∀ a₀ a, InitAbs a₀ → (existsAbs lts α).CanReach a₀ a →
      ¬ BadAbs a) :
    ∀ s₀ t, Init s₀ → lts.CanReach s₀ t → ¬ Bad t := by
  intro s₀ t hInit0 hReach hBad0
  exact hSafe (α s₀) (α t) (hInit s₀ hInit0)
    (existsAbs_canReach lts α hReach) (hBad t hBad0)

/-- Constrained reachability sets for testing feasibility of an abstract
path: index `0` holds the initial states abstracting to `p 0`; index
`n + 1` holds the states abstracting to `p (n + 1)` reached by one step from
index `n`. Abstract safety conclusions are safety (reachability) only: no
liveness and no ACTL* or CEGAR claim. -/
def constrainedReach {S T Label : Type*} (lts : LTS S Label) (α : S → T)
    (Init : S → Prop) (p : ℕ → T) (μ : ℕ → Label) : ℕ → Set S
  | 0 => {s | Init s ∧ α s = p 0}
  | n + 1 => {t | α t = p (n + 1) ∧
      ∃ s ∈ constrainedReach lts α Init p μ n, lts.Tr s (μ n) t}

/-- Membership in the constrained set at index `0`. Abstract safety
conclusions are safety (reachability) only: no liveness and no ACTL* or
CEGAR claim. -/
theorem mem_constrainedReach_zero {S T Label : Type*} (lts : LTS S Label)
    (α : S → T) (Init : S → Prop) (p : ℕ → T) (μ : ℕ → Label) (t : S) :
    t ∈ constrainedReach lts α Init p μ 0 ↔ Init t ∧ α t = p 0 := by
  simp [constrainedReach]

/-- Membership in the constrained set at index `n + 1`. Abstract safety
conclusions are safety (reachability) only: no liveness and no ACTL* or
CEGAR claim. -/
theorem mem_constrainedReach_succ {S T Label : Type*} (lts : LTS S Label)
    (α : S → T) (Init : S → Prop) (p : ℕ → T) (μ : ℕ → Label) (n : ℕ)
    (t : S) :
    t ∈ constrainedReach lts α Init p μ (n + 1) ↔
      α t = p (n + 1) ∧
        ∃ s ∈ constrainedReach lts α Init p μ n, lts.Tr s (μ n) t := by
  simp [constrainedReach]

/-- Membership in the constrained set at index `k` holds iff one single
consistent concrete sequence realizes the whole abstract prefix. Abstract
safety conclusions are safety (reachability) only: no liveness and no ACTL*
or CEGAR claim. -/
theorem mem_constrainedReach_iff {S T Label : Type*} (lts : LTS S Label)
    (α : S → T) (Init : S → Prop) (p : ℕ → T) (μ : ℕ → Label) (k : ℕ)
    (t : S) :
    t ∈ constrainedReach lts α Init p μ k ↔
      ∃ ss : ℕ → S, ss k = t ∧ Init (ss 0) ∧ (∀ i ≤ k, α (ss i) = p i) ∧
        (∀ i < k, lts.Tr (ss i) (μ i) (ss (i + 1))) := by
  induction k generalizing t with
  | zero =>
    rw [mem_constrainedReach_zero]
    constructor
    · rintro ⟨hInit, hα0⟩
      refine ⟨fun _ => t, rfl, hInit, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        exact hα0
      · intro i hi
        exact absurd hi (by omega)
    · rintro ⟨ss, hss, hInit, hα, -⟩
      rw [← hss]
      exact ⟨hInit, hα 0 (by omega)⟩
  | succ k ih =>
    constructor
    · intro h
      rw [mem_constrainedReach_succ] at h
      obtain ⟨hαt, s, hsC, hTr⟩ := h
      rw [ih s] at hsC
      obtain ⟨ss, hssk, hInit, hα, hTrSeq⟩ := hsC
      refine ⟨fun i => if i = k + 1 then t else ss i, ?_, ?_, ?_, ?_⟩
      · simp
      · have h0 : (0 : ℕ) ≠ k + 1 := by omega
        have hif : (fun i => if i = k + 1 then t else ss i) 0 = ss 0 := by
          change (if (0 : ℕ) = k + 1 then t else ss 0) = ss 0
          exact ite_eq_right h0
        rw [hif]
        exact hInit
      · intro i hi
        by_cases h : i = k + 1
        · subst h
          have hif :
              (fun j => if j = k + 1 then t else ss j) (k + 1) = t := by
            simp
          rw [hif]
          exact hαt
        · have hif :
              (fun j => if j = k + 1 then t else ss j) i = ss i := by
            change (if i = k + 1 then t else ss i) = ss i
            exact ite_eq_right h
          rw [hif]
          exact hα i (by omega)
      · intro i hi
        by_cases h : i + 1 = k + 1
        · have hne : i ≠ k + 1 := by omega
          have h1 :
              (fun j => if j = k + 1 then t else ss j) i = ss i := by
            change (if i = k + 1 then t else ss i) = ss i
            exact ite_eq_right hne
          have h2 :
              (fun j => if j = k + 1 then t else ss j) (i + 1) = t := by
            change (if i + 1 = k + 1 then t else ss (i + 1)) = t
            exact ite_eq_left h
          rw [h1, h2]
          have hik : i = k := by omega
          rw [hik, hssk]
          exact hTr
        · have hne : i ≠ k + 1 := by omega
          have h1 :
              (fun j => if j = k + 1 then t else ss j) i = ss i := by
            change (if i = k + 1 then t else ss i) = ss i
            exact ite_eq_right hne
          have h2 : (fun j => if j = k + 1 then t else ss j) (i + 1) =
              ss (i + 1) := by
            change (if i + 1 = k + 1 then t else ss (i + 1)) = ss (i + 1)
            exact ite_eq_right h
          rw [h1, h2]
          exact hTrSeq i (by omega)
    · rintro ⟨ss, hss, hInit, hα, hTrSeq⟩
      rw [mem_constrainedReach_succ]
      refine ⟨?_, ss k, ?_, ?_⟩
      · rw [← hss]
        exact hα (k + 1) (by omega)
      · rw [ih (ss k)]
        exact ⟨ss, rfl, hInit, fun i hi => hα i (by omega),
          fun i hi => hTrSeq i (by omega)⟩
      · have h := hTrSeq k (by omega)
        rw [hss] at h
        exact h

/-- Spuriousness criterion: the constrained set at index `k` is empty iff no
single consistent concrete sequence realizes the abstract path. Abstract
safety conclusions are safety (reachability) only: no liveness and no ACTL*
or CEGAR claim. -/
theorem constrainedReach_eq_empty_iff {S T Label : Type*} (lts : LTS S Label)
    (α : S → T) (Init : S → Prop) (p : ℕ → T) (μ : ℕ → Label) (k : ℕ) :
    constrainedReach lts α Init p μ k = ∅ ↔
      ¬ ∃ ss : ℕ → S, Init (ss 0) ∧ (∀ i ≤ k, α (ss i) = p i) ∧
        (∀ i < k, lts.Tr (ss i) (μ i) (ss (i + 1))) := by
  constructor
  · intro hC hEx
    obtain ⟨ss, hInit, hα, hTr⟩ := hEx
    have hmem : ss k ∈ constrainedReach lts α Init p μ k :=
      (mem_constrainedReach_iff lts α Init p μ k (ss k)).mpr
        ⟨ss, rfl, hInit, hα, hTr⟩
    rw [hC] at hmem
    exact hmem
  · intro hNo
    apply Set.Subset.antisymm _ (Set.empty_subset _)
    intro x hx
    rw [mem_constrainedReach_iff] at hx
    obtain ⟨ss, -, hInit, hα, hTr⟩ := hx
    exact absurd ⟨ss, hInit, hα, hTr⟩ hNo

#print axioms existsAbs

#print axioms existsAbs_tr_iff

#print axioms isSimulation_existsAbs

#print axioms existsAbs_mtr

#print axioms existsAbs_canReach

#print axioms safe_of_existsAbs

#print axioms safe_of_existsAbs_over

#print axioms constrainedReach

#print axioms mem_constrainedReach_zero

#print axioms mem_constrainedReach_succ

#print axioms mem_constrainedReach_iff

#print axioms constrainedReach_eq_empty_iff

end LTS

end Cslib
