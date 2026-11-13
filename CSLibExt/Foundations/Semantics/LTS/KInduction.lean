/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.OmegaRun

/-!
# k-induction

`k`-induction proves that a state property `P` holds at every reachable state
of a labelled transition system from two checks:

* base case: `P` holds at the last state of every run prefix of length
  `n < k` from an initial state (bounded model checking to depth `k - 1`);
* step case: every run prefix of length `k` whose first `k` states satisfy `P`
  ends in a state satisfying `P`.

Both checks quantify over finite run prefixes (`Cslib.LTS.FiniteRun`), so the
conclusion covers every state that `Cslib.LTS.CanReach` reaches from an initial
state, including deadlocked states that no infinite run visits. The step case
ranges over all run prefixes, reachable or not; it is not restricted to
loop-free prefixes.

This file covers the soundness core of roadmap package VER-37 of the Atlas TCS
canon roadmap. Completeness of bounded model checking is not claimed.

## Main results

* `Cslib.LTS.k_induction_finiteRun`: `P` holds at the last state of every run
  prefix from an initial state.
* `Cslib.LTS.k_induction_canReach`: `P` holds at every state reachable from an
  initial state.
* `Cslib.LTS.k_induction_sound`, `Cslib.LTS.safe_of_k_induction`: the
  infinite-path statements for a relation `step`, derived from
  `k_induction_canReach` on the restriction of `step` to the states that start
  an infinite path. They say nothing about states that no infinite path visits.

## References

* M. Sheeran, S. Singh, and G. Stålmarck, *Checking safety properties using
  induction and a SAT-solver*, Formal Methods in Computer-Aided Design
  (FMCAD 2000), LNCS 1954, Springer, 2000, pp. 108–125.
-/

@[expose] public section

namespace Cslib.LTS

section FiniteRuns

variable {State Label : Type*} {lts : LTS State Label}

/-- `k`-induction over finite runs: if the last state of every run prefix of
length `n < k` from an initial state satisfies `P` (base case), and every run
prefix of length `k` whose first `k` states satisfy `P` ends in a state
satisfying `P` (step case), then the last state of every run prefix from an
initial state satisfies `P`. -/
theorem k_induction_finiteRun {init P : State → Prop} {k : ℕ}
    (hbase : ∀ (ss : ℕ → State) (n : ℕ), init (ss 0) →
      lts.FiniteRun ss n → n < k → P (ss n))
    (hstep : ∀ ss : ℕ → State, lts.FiniteRun ss k →
      (∀ i, i < k → P (ss i)) → P (ss k))
    {ss : ℕ → State} {n : ℕ} (hinit : init (ss 0))
    (hrun : lts.FiniteRun ss n) : P (ss n) := by
  have hall : ∀ N m, m < N → m ≤ n → P (ss m) := by
    intro N
    induction N with
    | zero =>
      intro m hm
      exact absurd hm (Nat.not_lt_zero m)
    | succ N ih =>
      intro m hm hmn
      by_cases hmk : m < k
      · exact hbase ss m hinit (finiteRun_mono hrun hmn) hmk
      · have hwin : lts.FiniteRun (Semantics.shiftSeq ss (m - k)) k :=
          finiteRun_shift (finiteRun_mono hrun (by omega))
        have h := hstep _ hwin fun i _ => ih (i + (m - k)) (by omega) (by omega)
        change P (ss (k + (m - k))) at h
        rwa [show k + (m - k) = m by omega] at h
  exact hall (n + 1) n (Nat.lt_succ_self n) le_rfl

/-- `k`-induction soundness: under the base and step cases of
`k_induction_finiteRun`, every state reachable from an initial state satisfies
`P`, deadlocked states included. -/
theorem k_induction_canReach {init P : State → Prop} {k : ℕ}
    (hbase : ∀ (ss : ℕ → State) (n : ℕ), init (ss 0) →
      lts.FiniteRun ss n → n < k → P (ss n))
    (hstep : ∀ ss : ℕ → State, lts.FiniteRun ss k →
      (∀ i, i < k → P (ss i)) → P (ss k))
    {s₀ s : State} (hinit : init s₀) (hreach : lts.CanReach s₀ s) : P s := by
  obtain ⟨ss, n, h0, hn, hrun⟩ := exists_finiteRun_of_canReach hreach
  subst h0 hn
  exact k_induction_finiteRun hbase hstep hinit hrun

end FiniteRuns

section InfinitePaths

variable {S : Type*}

/-- `s` starts an infinite path of `step`. -/
private def StartsPath (step : S → S → Prop) (s : S) : Prop :=
  ∃ p : ℕ → S, p 0 = s ∧ ∀ i, step (p i) (p (i + 1))

/-- `step` restricted to the states that start an infinite path. -/
private def pathLTS (step : S → S → Prop) :
    LTS {s // StartsPath step s} Unit :=
  ⟨fun a _ b => step a.1 b.1⟩

/-- Every state of an infinite path starts an infinite path, its suffix. -/
private theorem startsPath_apply {step : S → S → Prop} {p : ℕ → S}
    (hpath : ∀ i, step (p i) (p (i + 1))) (j : ℕ) : StartsPath step (p j) := by
  refine ⟨Semantics.shiftSeq p j, ?_, fun i => ?_⟩
  · change p (0 + j) = p j
    rw [Nat.zero_add]
  · change step (p (i + j)) (p (i + 1 + j))
    rw [Nat.add_right_comm]
    exact hpath (i + j)

/-- A run prefix of `pathLTS step`, continued by an infinite path from its last
state, is an infinite path of `step`. -/
private theorem exists_path_of_finiteRun {step : S → S → Prop}
    {ss : ℕ → {s // StartsPath step s}} {n : ℕ}
    (hrun : (pathLTS step).FiniteRun ss n) :
    ∃ p : ℕ → S, (∀ i, step (p i) (p (i + 1))) ∧
      ∀ i, i ≤ n → p i = (ss i).1 := by
  obtain ⟨w, hw0, hw⟩ := (ss n).2
  let p : ℕ → S := fun i => if i ≤ n then (ss i).1 else w (i - n)
  have hle : ∀ i, i ≤ n → p i = (ss i).1 := fun _ hi => ite_eq_left hi
  have hge : ∀ i, n ≤ i → p i = w (i - n) := by
    intro i hi
    by_cases hin : i ≤ n
    · have hieq : i = n := le_antisymm hin hi
      rw [hle i hin, hieq, Nat.sub_self, hw0]
    · exact ite_eq_right hin
  refine ⟨p, fun i => ?_, hle⟩
  by_cases hin : i < n
  · rw [hle i hin.le, hle (i + 1) hin]
    obtain ⟨_, h⟩ := hrun i hin
    exact h
  · rw [hge i (by omega), hge (i + 1) (by omega),
      show i + 1 - n = i - n + 1 by omega]
    exact hw (i - n)

/-- `k`-induction soundness for a transition system `step`
with initial states `init` and bad states `bad`, over
infinite paths: if no bad state occurs among the first `k`
states of any path from an initial state (base), and any
`k` consecutive bad-free states along a path are followed by
a bad-free state (step), then no path from an initial state
ever reaches a bad state.

Derived from `k_induction_canReach` on the restriction of `step` to the states
that start an infinite path. The conclusion covers only states on infinite
paths; `k_induction_canReach` covers every reachable state. -/
theorem k_induction_sound {step : S → S → Prop}
    {init bad : S → Prop} {k : ℕ}
    (hbase : ∀ p : ℕ → S, init (p 0) →
      (∀ i, step (p i) (p (i + 1))) → ∀ i, i < k → ¬ bad (p i))
    (hstep : ∀ p : ℕ → S, (∀ i, i < k → ¬ bad (p i)) →
      (∀ i, step (p i) (p (i + 1))) → ¬ bad (p k)) :
    ∀ p : ℕ → S, init (p 0) → (∀ i, step (p i) (p (i + 1))) →
      ∀ i, ¬ bad (p i) := by
  intro p hinit hpath i
  let q : ℕ → {s // StartsPath step s} := fun j =>
    ⟨p j, startsPath_apply hpath j⟩
  have hq : (pathLTS step).OmegaRun q := fun j => ⟨(), hpath j⟩
  refine k_induction_canReach (lts := pathLTS step) (init := fun a => init a.1)
    (P := fun a => ¬ bad a.1) (k := k) ?_ ?_ (s₀ := q 0) (s := q i) hinit
    (canReach_omegaRun_apply hq i)
  · intro ss n h0 hrun hn
    obtain ⟨r, hr, hagree⟩ := exists_path_of_finiteRun hrun
    have h := hbase r (by rw [hagree 0 (Nat.zero_le n)]; exact h0) hr n hn
    rwa [hagree n le_rfl] at h
  · intro ss hrun hsafe
    obtain ⟨r, hr, hagree⟩ := exists_path_of_finiteRun hrun
    have h := hstep r (fun i hi => by rw [hagree i hi.le]; exact hsafe i hi) hr
    rwa [hagree k le_rfl] at h

/-- State form of `k_induction_sound`: every state on an infinite path from an
initial state is safe. A reachable state that no infinite path visits, such as
a deadlocked one, is not covered; `k_induction_canReach` covers it. -/
theorem safe_of_k_induction {step : S → S → Prop}
    {init bad : S → Prop} {k : ℕ}
    (hbase : ∀ p : ℕ → S, init (p 0) →
      (∀ i, step (p i) (p (i + 1))) → ∀ i, i < k → ¬ bad (p i))
    (hstep : ∀ p : ℕ → S, (∀ i, i < k → ¬ bad (p i)) →
      (∀ i, step (p i) (p (i + 1))) → ¬ bad (p k))
    {s : S} (hreach : ∃ p : ℕ → S, init (p 0) ∧
      (∀ i, step (p i) (p (i + 1))) ∧ ∃ i, p i = s) :
    ¬ bad s := by
  obtain ⟨p, hinit, hpath, i, hi⟩ := hreach
  rw [← hi]
  exact k_induction_sound hbase hstep p hinit hpath i

end InfinitePaths

end Cslib.LTS
