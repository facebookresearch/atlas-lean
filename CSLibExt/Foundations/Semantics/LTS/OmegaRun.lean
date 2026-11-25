/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `85a3956f8d763f4003659b2ea871b54d9d9f711e`.
Original formalization by Adam Kiezun.
Adapted to the upstream `Cslib.LTS` type (its `Tr` relation and `MTr`
multistep transitions).
-/

/-
# Finite and infinite runs
-/
module

public import CSLibExt.Foundations.Semantics.LTS.Basic

/-!
# Finite and infinite runs

Temporal logics quantify over sequences of states and forget the labels
that witness each transition.  This file supplies that carrier over the
upstream `Cslib.LTS`: finite run prefixes and infinite runs, their relation
to multistep transitions and reachability, and suffix shifts of sequences.
-/

@[expose] public section

namespace Cslib.Semantics

/-- **Shifted sequence.** For a sequence $s_0, s_1, s_2, \dots$ and a natural number $k$, the shift
of the sequence by $k$ is the sequence whose $i$-th term is $s_{i+k}$; that is, the suffix
starting at index $k$, re-indexed from $0$. -/
def shiftSeq {State : Type*} (ss : ℕ → State) (k : ℕ) : ℕ → State :=
  fun i => ss (i + k)

theorem shiftSeq_zero {State : Type*} (ss : ℕ → State) :
    shiftSeq ss 0 = ss := by
  funext i
  rfl

theorem shiftSeq_add {State : Type*} (ss : ℕ → State) (a b : ℕ) :
    shiftSeq (shiftSeq ss a) b = shiftSeq ss (a + b) := by
  funext i
  change ss (i + b + a) = ss (i + (a + b))
  congr 1
  omega

end Cslib.Semantics

namespace Cslib

namespace LTS

variable {State Label : Type*} (lts : LTS State Label)

/-- **Finite run.** In a labelled transition system, a sequence of states $s_0, s_1, s_2, \dots$
is a finite run of length $k$ when for every $i < k$ there is a label $a$ such that there is a
transition from $s_i$ to $s_{i+1}$ labelled $a$.

The states after index $k$ are unconstrained. -/
def FiniteRun (ss : ℕ → State) (k : ℕ) : Prop :=
  ∀ i, i < k → ∃ label, lts.Tr (ss i) label (ss (i + 1))

/-- **Infinite run.** In a labelled transition system, a sequence of states $s_0, s_1, s_2, \dots$
is an infinite run when for every $i$ there is a label $a$ such that there is a transition from
$s_i$ to $s_{i+1}$ labelled $a$. -/
def OmegaRun (ss : ℕ → State) : Prop :=
  ∀ i, ∃ label, lts.Tr (ss i) label (ss (i + 1))

variable {lts}

theorem finiteRun_zero {ss : ℕ → State} : lts.FiniteRun ss 0 := by
  intro i hi
  exact (Nat.not_lt_zero i hi).elim

theorem finiteRun_mono {ss : ℕ → State} {j k : ℕ}
    (h : lts.FiniteRun ss k) (hjk : j ≤ k) : lts.FiniteRun ss j := by
  intro i hi
  exact h i (by omega)

theorem omegaRun_finiteRun {ss : ℕ → State} {k : ℕ}
    (h : lts.OmegaRun ss) : lts.FiniteRun ss k := by
  intro i _
  exact h i

theorem finiteRun_canReach {ss : ℕ → State} {k : ℕ}
    (h : lts.FiniteRun ss k) : lts.CanReach (ss 0) (ss k) := by
  induction k with
  | zero => exact CanReach.refl _ _
  | succ k ih =>
      have hpre : lts.FiniteRun ss k := finiteRun_mono h (by omega)
      have hrec : lts.CanReach (ss 0) (ss k) := ih hpre
      obtain ⟨label, hstep⟩ := h k (by omega)
      exact hrec.trans ⟨[label], MTr.stepL hstep MTr.refl⟩

theorem canReach_omegaRun_apply {ss : ℕ → State}
    (h : lts.OmegaRun ss) (k : ℕ) : lts.CanReach (ss 0) (ss k) :=
  finiteRun_canReach (omegaRun_finiteRun h)

theorem exists_finiteRun_of_mtr {s t : State} {labels : List Label}
    (h : lts.MTr s labels t) :
    ∃ ss : ℕ → State, ss 0 = s ∧ ss labels.length = t ∧
      lts.FiniteRun ss labels.length := by
  induction h with
  | refl =>
      rename_i st
      exact ⟨fun _ => st, rfl, rfl, finiteRun_zero⟩
  | stepL head tail ih =>
      rename_i src lab mid _labs _tgt
      obtain ⟨ss', h0, hlen, hrun⟩ := ih
      refine ⟨fun i => match i with | 0 => src | i + 1 => ss' i,
        rfl, ?_, ?_⟩
      · simp only [List.length_cons]
        exact hlen
      · intro i hi
        simp only [List.length_cons] at hi
        cases i with
        | zero =>
            refine ⟨lab, ?_⟩
            change lts.Tr src lab (ss' 0)
            rw [h0]
            exact head
        | succ i =>
            exact hrun i (by omega)

theorem exists_finiteRun_of_canReach {s t : State}
    (h : lts.CanReach s t) :
    ∃ (ss : ℕ → State) (k : ℕ), ss 0 = s ∧ ss k = t ∧
      lts.FiniteRun ss k := by
  obtain ⟨labels, htrace⟩ := h
  obtain ⟨ss, h0, hlen, hrun⟩ := exists_finiteRun_of_mtr htrace
  exact ⟨ss, labels.length, h0, hlen, hrun⟩

theorem omegaRun_shift {ss : ℕ → State}
    (h : lts.OmegaRun ss) (k : ℕ) :
    lts.OmegaRun (Semantics.shiftSeq ss k) := by
  intro i
  change ∃ label, lts.Tr (ss (i + k)) label (ss (i + 1 + k))
  obtain ⟨label, hstep⟩ := h (i + k)
  refine ⟨label, ?_⟩
  have hidx : i + 1 + k = i + k + 1 := by omega
  rw [hidx]
  exact hstep

theorem finiteRun_shift {ss : ℕ → State} {j k : ℕ}
    (h : lts.FiniteRun ss (j + k)) :
    lts.FiniteRun (Semantics.shiftSeq ss j) k := by
  intro i hi
  change ∃ label, lts.Tr (ss (i + j)) label (ss (i + 1 + j))
  have hlt : i + j < j + k := by omega
  obtain ⟨label, hstep⟩ := h (i + j) hlt
  refine ⟨label, ?_⟩
  have hidx : i + 1 + j = i + j + 1 := by omega
  rw [hidx]
  exact hstep

/-- **Invariant principle for infinite runs.** Let $P$ be a predicate on the states of a labelled
transition system such that, whenever $P(s)$ holds and there is a transition from $s$ to $t$ with
some label, $P(t)$ holds. Then for every infinite run $s_0, s_1, s_2, \dots$ with $P(s_0)$, the
predicate $P(s_k)$ holds for every $k$. -/
theorem forall_state_of_invariant {run : ℕ → State}
    (hrun : lts.OmegaRun run) {P : State → Prop} (h0 : P (run 0))
    (hstep : ∀ s t, P s → lts.UnlabelledTr s t → P t) :
    ∀ k, P (run k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => exact hstep _ _ ih (hrun k)

end LTS

end Cslib
