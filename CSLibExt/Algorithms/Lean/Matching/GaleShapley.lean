/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matching.GaleShapley
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The Gale-Shapley deferred-acceptance algorithm

Gale and Shapley, *College Admissions and the Stability of Marriage*, American Mathematical
Monthly 69 (1962); Kleinberg and Tardos, *Algorithm Design*, Section 1.1. MathlibExt's
`MathlibExt/Combinatorics/Matching/GaleShapley.lean` proves that a stable perfect matching exists
(`gale_shapley_exists_stable_matching`) with a private, noncomputable deferred-acceptance run. This
module is the executable algorithm with its CS-facing guarantees, stated in MathlibExt's
vocabulary (`MPrefs`, `WPrefs`, `PerfectMatching`, `IsStable`) so the two developments share one
notion of stability.

`n` proposers and `n` receivers are both `Fin n`. A preference is a ranking `σ : Equiv.Perm (Fin n)`
(`σ k` is the `k`-th choice); `toOrder σ`, `mprefs`, `wprefs` are the corresponding MathlibExt
preferences, and every MathlibExt preference on `Fin n` arises this way (`exists_toOrder_eq`).

Main results:

* `galeShapley`: the algorithm on arrays (`State`, `propose`, `chooser`, `run`): a free proposer
  proposes to his best receiver not yet proposed to, who keeps the better of him and her current
  partner (`newHolder`).
* `Inv`, `inv_propose`: the invariant, including Gale and Shapley's key fact that no proposer is
  ever rejected by a receiver he is matched to in some stable matching (`Inv.opt`).
* `sum_next_galeShapley_le`: **at most `n²` proposals** (each proposal advances one proposer's
  count, `sum_next_propose`), after which no free proposer can propose (`galeShapley_spec`).
* `gsMatching`: **the output is a perfect matching** (`held_of_done`, `holds_of_held`).
* `isStable_gsMatching`: **it is stable** in MathlibExt's sense.
* `gsMatching_proposer_optimal`: **proposer-optimality**: no stable matching gives a proposer a
  better partner; `gsMatching_receiver_pessimal`: **receiver-pessimality**: no stable matching
  gives a receiver a worse partner.
* `exists_rankings_gsMatching`: every MathlibExt preference profile on `Fin n` is presented by
  rankings whose Gale-Shapley matching is stable and proposer-optimal for it.

## Cost model

The cost is the number of proposals, at most `n * n` (`sum_next_galeShapley_le`); `run` stops as
soon as no proposer can propose. Each proposal also scans for a free proposer (`chooser`, `O(n²)`
reads), so the array implementation takes `O(n⁴)` steps; the textbook `O(n²)` needs a queue of
free proposers, not implemented here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matching.GaleShapley

open MathlibExt.Combinatorics.Matching.GaleShapley (MPrefs WPrefs PerfectMatching IsStable
  IsBlockingPair)

variable {n : ℕ}

/-! ## Preferences -/

/-- **Preference order of a ranking.** A permutation $\sigma$ of $\{0, \dots, n-1\}$, read as a
ranking ($\sigma(k)$ is the $k$-th choice, $\sigma(0)$ the best), gives the strict total order on
$\{0, \dots, n-1\}$ in which $a$ is preferred to $b$ when $\sigma^{-1}(a) < \sigma^{-1}(b)$. -/
def toOrder (σ : Equiv.Perm (Fin n)) : MathlibExt.Order.StrictTotalOrder (Fin n) where
  lt a b := σ.symm a < σ.symm b
  irrefl _ := lt_irrefl _
  trans h1 h2 := lt_trans h1 h2
  total h := lt_or_gt_of_ne fun e => h (σ.symm.injective e)

/-- **Proposers' preferences from rankings.** Given for each proposer $m$ a ranking $\sigma_m$ of
the $n$ receivers ($\sigma_m(k)$ is the choice of $m$ of rank $k$, rank $0$ the best), the
proposers' preference profile assigns to $m$ the strict total order in which $m$ prefers $w$ to
$w'$ when $\sigma_m^{-1}(w) < \sigma_m^{-1}(w')$. -/
def mprefs (mp : Fin n → Equiv.Perm (Fin n)) : MPrefs (Fin n) (Fin n) := fun m => toOrder (mp m)

/-- **Receivers' preference profile from rankings.** Given for each receiver $w$ a ranking
$\sigma_w$ of the $n$ proposers (a permutation of $\{0, \dots, n-1\}$, with $\sigma_w(0)$ her first
choice), the receivers' preference profile assigns to $w$ the preference order of $\sigma_w$: $w$
prefers $a$ to $b$ when $\sigma_w^{-1}(a) < \sigma_w^{-1}(b)$. -/
def wprefs (wp : Fin n → Equiv.Perm (Fin n)) : WPrefs (Fin n) (Fin n) := fun w => toOrder (wp w)

/-! ## The algorithm -/

/-- **Deferred-acceptance state.** A state of deferred acceptance with $n$ proposers and $n$
receivers, both numbered $0, \dots, n-1$, records for each proposer a natural number, the number of
proposals he has made (his next proposal goes to his choice of that rank), and for each receiver
either the proposer she currently holds or that she holds nobody. -/
structure State (n : ℕ) where
  /-- The number of proposals made by each proposer. -/
  next : Vector ℕ n
  /-- The proposer each receiver holds, if any. -/
  holder : Vector (Option (Fin n)) n

/-- **Initial state of deferred acceptance.** The initial state with $n$ proposers and
$n$ receivers: every proposer has made $0$ proposals and no receiver holds anyone. -/
def init (n : ℕ) : State n := ⟨Vector.replicate n 0, Vector.replicate n none⟩

/-- **Free proposer.** A proposer $m$ is free in a state $s$ of deferred acceptance when no
receiver holds $m$ in $s$. -/
def Free (s : State n) (m : Fin n) : Prop := ∀ w : Fin n, s.holder[w] ≠ some m

instance (s : State n) (m : Fin n) : Decidable (Free s m) := by unfold Free; infer_instance

variable (mp wp : Fin n → Equiv.Perm (Fin n))

/-- **Receiver's holder after a proposal.** In a state $s$ of deferred acceptance, the proposer
whom receiver $w$ holds after proposer $m$ proposes to her is $m$ if she holds nobody in $s$ or
ranks $m$ strictly better than her current holder $m'$ in her ranking, and $m'$ otherwise. -/
def newHolder (s : State n) (m w : Fin n) : Option (Fin n) :=
  match s.holder[w] with
  | none => some m
  | some m' => if (wp w).symm m < (wp w).symm m' then some m else some m'

/-- **A proposal.** Fix, for each proposer, a ranking of the $n$ receivers and, for each receiver,
a ranking of the $n$ proposers (rank $0$ is the first choice). Let $s$ be a state of deferred
acceptance in which proposer $m$ has made $k$ proposals. If $k < n$, then $m$ proposes to the
receiver $w$ of rank $k$ in his ranking: his number of proposals becomes $k + 1$, and $w$ now
holds $m$ if she held nobody or ranks $m$ strictly above the proposer she held, and keeps her old
holder otherwise; all other counts and holders are unchanged. If $k \ge n$, the state is
unchanged. -/
def propose (s : State n) (m : Fin n) : State n :=
  if h : s.next[m] < n then
    ⟨s.next.set m (s.next[m] + 1),
      s.holder.set (mp m ⟨s.next[m], h⟩) (newHolder wp s m (mp m ⟨s.next[m], h⟩))⟩
  else s

/-- **Choosing the next proposer.** In a state $s$ of deferred acceptance with proposers
$0, 1, \dots, n-1$, the chooser returns the least proposer $m$ who is free in $s$ and has made
fewer than $n$ proposals in $s$, or no proposer if there is none. -/
def chooser (s : State n) : Option (Fin n) :=
  (List.finRange n).find? fun m => decide (Free s m) && decide (s.next[m] < n)

/-- **Running deferred acceptance.** Fix rankings for $n$ proposers and $n$ receivers, both
numbered $0, \dots, n-1$. Starting from a state $s$ with a budget of $f$ proposals: if $f = 0$, or
if no proposer is both free (held by no receiver) and has made fewer than $n$ proposals, the run
returns $s$; otherwise the lowest-numbered such proposer makes a proposal, and the run continues
from the resulting state with budget $f - 1$. -/
def run : ℕ → State n → State n
  | 0, s => s
  | fuel + 1, s =>
      match chooser s with
      | none => s
      | some m => run fuel (propose mp wp s m)

/-- **Deferred acceptance.** Let each of $n$ proposers rank the $n$ receivers, and each receiver
rank the $n$ proposers, with rank $0$ the best. Deferred acceptance is the state reached from the
initial state, in which no one has proposed and no receiver holds anyone, by repeating the
following step at most $n^2$ times, stopping early once no proposer is both free and has made
fewer than $n$ proposals: the least such proposer, having made $p$ proposals so far, proposes to
the receiver of rank $p$ in his ranking, and she then holds whichever of him and her current
holder she ranks better, or him if she held no one.

These $n^2$ steps always suffice: in the resulting state no proposer is both free and has made
fewer than $n$ proposals. -/
def galeShapley : State n := run mp wp (n * n) (init n)

/-! ## Accessors -/

variable {mp wp}

private theorem vget_set {α : Type*} (v : Vector α n) (i j : Fin n) (x : α) :
    (v.set i x)[j] = if j = i then x else v[j] := by
  simp only [Fin.getElem_fin]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff, eq_comm]

theorem next_propose {s : State n} {m : Fin n} (h : s.next[m] < n) (m' : Fin n) :
    (propose mp wp s m).next[m'] = if m' = m then s.next[m] + 1 else s.next[m'] := by
  unfold propose
  split
  · exact vget_set _ _ _ _
  · contradiction

theorem holder_propose {s : State n} {m : Fin n} (h : s.next[m] < n) (w' : Fin n) :
    (propose mp wp s m).holder[w'] = if w' = mp m ⟨s.next[m], h⟩
      then newHolder wp s m (mp m ⟨s.next[m], h⟩) else s.holder[w'] := by
  unfold propose
  split
  · exact vget_set _ _ _ _
  · contradiction

theorem propose_of_not_lt {s : State n} {m : Fin n} (h : ¬ s.next[m] < n) :
    propose mp wp s m = s := by
  unfold propose
  split
  · contradiction
  · rfl

theorem chooser_some {s : State n} {m : Fin n} (h : chooser s = some m) :
    Free s m ∧ s.next[m] < n := by
  have := List.find?_some h
  simpa using this

theorem chooser_none {s : State n} (h : chooser s = none) (m : Fin n) :
    ¬ (Free s m ∧ s.next[m] < n) := by
  have := List.find?_eq_none.1 h m (List.mem_finRange m)
  simpa using this

/-! ## The invariant -/

variable (mp wp) in
/-- **Invariant of deferred acceptance.** Let each proposer $m$ have a ranking $\sigma_m$ of the
$n$ receivers and each receiver $w$ a ranking $\tau_w$ of the $n$ proposers, where $\sigma_m(k)$
is the choice of $m$ of rank $k$ (rank $0$ is the best) and $\tau_w^{-1}(x)$ is the rank of $x$
for $w$. A state $s$ of deferred acceptance satisfies the invariant when: every proposer has made
at most $n$ proposals; if $w$ holds $m$, then $m$ has made $k + 1$ proposals for some rank $k$
with $\sigma_m(k) = w$; no proposer is held by two different receivers; for every proposer $m$
and every rank $k$ less than the number of proposals of $m$, the receiver $w = \sigma_m(k)$ holds
some $m'$ with $\tau_w^{-1}(m') \le \tau_w^{-1}(m)$; and for such $m$ and $k$, if $\sigma_m(k)$
does not hold $m$, then no perfect matching that is stable for the preferences given by the
rankings matches $m$ with $\sigma_m(k)$. -/
structure Inv (s : State n) : Prop where
  /-- Nobody proposes more than `n` times. -/
  next_le : ∀ m : Fin n, s.next[m] ≤ n
  /-- A held proposer is held by his latest proposal. -/
  last : ∀ w m : Fin n, s.holder[w] = some m → ∃ k : Fin n, k.val + 1 = s.next[m] ∧ mp m k = w
  /-- A proposer is held by at most one receiver. -/
  inj : ∀ w w' m : Fin n, s.holder[w] = some m → s.holder[w'] = some m → w = w'
  /-- A receiver who was proposed to holds someone at least as good as each of her proposers. -/
  held : ∀ m k : Fin n, k.val < s.next[m] →
    ∃ m', s.holder[mp m k] = some m' ∧ (wp (mp m k)).symm m' ≤ (wp (mp m k)).symm m
  /-- **No proposer is rejected by a stable partner** (Gale and Shapley's optimality argument). -/
  opt : ∀ m k : Fin n, k.val < s.next[m] → s.holder[mp m k] ≠ some m →
    ∀ ν : PerfectMatching (Fin n) (Fin n), IsStable (mprefs mp) (wprefs wp) ν → ν m ≠ mp m k

theorem inv_init : Inv mp wp (init n) := by
  refine ⟨fun m => by simp [init], fun w m h => by simp [init] at h,
    fun w w' m h => by simp [init] at h, fun m k hk => by simp [init] at hk,
    fun m k hk => by simp [init] at hk⟩

/-- **A stable matching has no blocking pair.** Let each proposer $m$ have a ranking $\sigma_m$ of
the $n$ receivers and each receiver $w$ a ranking $\tau_w$ of the $n$ proposers, where
$\sigma_m^{-1}(x)$ and $\tau_w^{-1}(x)$ are ranks ($0$ the best). If $\nu$ is a perfect matching
that is stable for the preferences given by these rankings, there are no proposer $m$ and
receiver $w$ with $\sigma_m^{-1}(w) < \sigma_m^{-1}(\nu(m))$ and
$\tau_w^{-1}(m) < \tau_w^{-1}(\nu^{-1}(w))$. -/
theorem not_blocking {ν : PerfectMatching (Fin n) (Fin n)}
    (hν : IsStable (mprefs mp) (wprefs wp) ν) {m w : Fin n}
    (h1 : (mp m).symm w < (mp m).symm (ν m)) (h2 : (wp w).symm m < (wp w).symm (ν.symm w)) :
    False :=
  hν m w ⟨h1, h2⟩

/-- **Rejected proposals bound stable partners.** Let each proposer $m$ have a ranking
$\sigma_m$ of the $n$ receivers ($\sigma_m(k)$ is the choice of $m$ of rank $k$, rank $0$ the
best), and each receiver a ranking of the $n$ proposers. Let $s$ be a state of deferred
acceptance satisfying the invariant, let $\nu$ be a perfect matching that is stable for the
preferences given by the rankings, let $m$ be a proposer, and let $b$ be a natural number at most
the number of proposals $m$ has made in $s$. If for every rank $k < b$ the receiver $\sigma_m(k)$
does not hold $m$ in $s$, then $\sigma_m^{-1}(\nu(m)) \ge b$. -/
theorem le_rank_of_rejected {s : State n} (hI : Inv mp wp s) {ν : PerfectMatching (Fin n) (Fin n)}
    (hν : IsStable (mprefs mp) (wprefs wp) ν) (m : Fin n) {b : ℕ} (hb : b ≤ s.next[m])
    (hrej : ∀ k : Fin n, k.val < b → s.holder[mp m k] ≠ some m) :
    b ≤ ((mp m).symm (ν m)).val := by
  by_contra hlt
  push Not at hlt
  exact hI.opt m _ (by omega) (hrej _ hlt) ν hν (by simp)

private theorem vget_congr {α : Type*} (v : Vector α n) {a b : Fin n} (h : a = b) :
    v[a] = v[b] := by
  subst h; rfl

/-- **Cases of the receiver's new holder.** Let $s$ be a state of deferred acceptance, $m$ a
proposer and $w$ a receiver with ranking $\tau_w$ of the proposers ($\tau_w^{-1}(x)$ is the rank
of $x$, rank $0$ the best). Then one of the following holds: $w$ holds nobody in $s$ and holds $m$
after $m$ proposes to her; or $w$ holds some $y$ in $s$ with $\tau_w^{-1}(m) < \tau_w^{-1}(y)$
and holds $m$ after $m$ proposes to her; or $w$ holds some $y$ in $s$ with
$\tau_w^{-1}(m) \ge \tau_w^{-1}(y)$ and holds $y$ after $m$ proposes to her. -/
theorem newHolder_cases (s : State n) (m w : Fin n) :
    (s.holder[w] = none ∧ newHolder wp s m w = some m) ∨
    (∃ y, s.holder[w] = some y ∧ (wp w).symm m < (wp w).symm y ∧ newHolder wp s m w = some m) ∨
    (∃ y, s.holder[w] = some y ∧ ¬ (wp w).symm m < (wp w).symm y ∧
      newHolder wp s m w = some y) := by
  unfold newHolder
  cases hw : s.holder[w] with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some y =>
      by_cases hl : (wp w).symm m < (wp w).symm y
      · exact Or.inr (Or.inl ⟨y, rfl, hl, by simp [hl]⟩)
      · exact Or.inr (Or.inr ⟨y, rfl, hl, by simp [hl]⟩)

theorem inv_propose {s : State n} (hI : Inv mp wp s) {m : Fin n} (hfree : Free s m)
    (h : s.next[m] < n) : Inv mp wp (propose mp wp s m) := by
  set j : Fin n := ⟨s.next[m], h⟩ with hj
  set w := mp m j with hw
  have hnext := next_propose (mp := mp) (wp := wp) h
  have hhold := holder_propose (mp := mp) (wp := wp) h
  rw [← hj, ← hw] at hhold
  have hcases := newHolder_cases (wp := wp) s m w
  have hholdw : (propose mp wp s m).holder[w] = newHolder wp s m w := by
    simp only [hhold, ↓reduceIte]
  -- who can be held after the proposal
  have hnew : ∀ w' x, (propose mp wp s m).holder[w'] = some x →
      s.holder[w'] = some x ∨ (w' = w ∧ x = m) := by
    intro w' x hx
    rw [hhold] at hx
    split_ifs at hx with e
    · subst e
      rcases hcases with ⟨-, hn⟩ | ⟨y, -, -, hn⟩ | ⟨y, hy, -, hn⟩
      · rw [hn] at hx; cases hx; exact Or.inr ⟨rfl, rfl⟩
      · rw [hn] at hx; cases hx; exact Or.inr ⟨rfl, rfl⟩
      · rw [hn] at hx; cases hx; exact Or.inl hy
    · exact Or.inl hx
  -- earlier proposals of `m` went elsewhere
  have hprev : ∀ k : Fin n, k.val < s.next[m] → mp m k ≠ w := by
    intro k hk e
    have := (mp m).injective e
    rw [hj] at this
    have := congrArg Fin.val this
    simp only at this
    omega
  have hkj : ∀ k : Fin n, k.val < s.next[m] + 1 → k.val ≠ s.next[m] → k.val < s.next[m] := by
    intro k h1 h2; omega
  refine ⟨fun m' => ?_, fun w' m' hx => ?_, fun w1 w2 x h1 h2 => ?_, fun m' k hk => ?_,
    fun m' k hk hrej ν hν hνk => ?_⟩
  · -- next_le
    rw [hnext]
    split_ifs
    · omega
    · exact hI.next_le m'
  · -- last
    rcases hnew w' m' hx with hold | ⟨rfl, rfl⟩
    · have hm' : m' ≠ m := fun e => hfree w' (e ▸ hold)
      obtain ⟨k, hk, hkw⟩ := hI.last w' m' hold
      exact ⟨k, by simp only [hnext, hm', ↓reduceIte]; exact hk, hkw⟩
    · exact ⟨j, by simp only [hnext, ↓reduceIte]; rfl, rfl⟩
  · -- inj
    rcases hnew w1 x h1 with o1 | ⟨e1, ex1⟩ <;> rcases hnew w2 x h2 with o2 | ⟨e2, ex2⟩
    · exact hI.inj w1 w2 x o1 o2
    · subst ex2; exact absurd o1 (hfree w1)
    · subst ex1; exact absurd o2 (hfree w2)
    · rw [e1, e2]
  · -- held
    by_cases hmk : m' = m ∧ k = j
    · obtain ⟨e1, e2⟩ := hmk
      have hxw : mp m' k = w := by rw [e1, e2]
      rw [vget_congr _ hxw, hholdw, hxw, e1]
      rcases hcases with ⟨-, hn⟩ | ⟨y, -, -, hn⟩ | ⟨y, -, hl, hn⟩
      · exact ⟨m, hn, le_rfl⟩
      · exact ⟨m, hn, le_rfl⟩
      · exact ⟨y, hn, not_lt.1 hl⟩
    · have hk' : k.val < s.next[m'] := by
        rw [hnext] at hk
        split_ifs at hk with e
        · subst e
          refine hkj k hk fun e' => hmk ⟨rfl, Fin.ext e'⟩
        · exact hk
      obtain ⟨y, hy, hle⟩ := hI.held m' k hk'
      rw [hhold]
      split_ifs with e
      · rw [vget_congr _ e] at hy
        rw [e] at hle ⊢
        rcases hcases with ⟨hn0, -⟩ | ⟨y', hy', hl, hn⟩ | ⟨y', hy', -, hn⟩
        · rw [hn0] at hy; cases hy
        · rw [hy'] at hy; cases hy
          exact ⟨m, hn, le_trans (le_of_lt hl) hle⟩
        · have hyy : y' = y := Option.some_injective _ (hy'.symm.trans hy)
          exact ⟨y', hn, by rw [hyy]; exact hle⟩
      · exact ⟨y, hy, hle⟩
  · -- opt
    by_cases hx : mp m' k = w
    · by_cases hm' : m' = m
      · subst hm'
        rw [hx] at hνk
        rw [vget_congr _ hx] at hrej
        simp only [hhold, ↓reduceIte] at hrej
        rcases hcases with ⟨-, hn⟩ | ⟨y, -, -, hn⟩ | ⟨y, hy, hl, hn⟩
        · exact hrej hn
        · exact hrej hn
        · -- `m'` was rejected for `y`
          have hym : y ≠ m' := fun e => hfree w (e ▸ hy)
          have hlt : (wp w).symm y < (wp w).symm m' :=
            lt_of_le_of_ne (not_lt.1 hl) fun e => hym ((wp w).symm.injective e)
          obtain ⟨k', hk', hk'w⟩ := hI.last w y hy
          have hνy : ν y ≠ w := fun e => hym (ν.injective (e.trans hνk.symm))
          have hb := le_rank_of_rejected hI hν y (b := k'.val) (by omega) fun k'' hk'' e => by
            have := hI.inj _ _ _ e hy
            rw [← hk'w] at this
            have := congrArg Fin.val ((mp y).injective this)
            omega
          have hne : ((mp y).symm (ν y)).val ≠ k'.val := fun e => hνy (by
            rw [← hk'w, ← Fin.ext e]; simp)
          have h1 : (mp y).symm w < (mp y).symm (ν y) := by
            rw [← hk'w, Equiv.symm_apply_apply]
            exact Fin.lt_def.2 (lt_of_le_of_ne hb (Ne.symm hne))
          have h2 : (wp w).symm y < (wp w).symm (ν.symm w) := by
            rw [show ν.symm w = m' from by rw [← hνk]; simp]
            exact hlt
          exact not_blocking hν h1 h2
      · have hk' : k.val < s.next[m'] := by simp only [hnext, hm', ↓reduceIte] at hk; exact hk
        by_cases hold : s.holder[mp m' k] = some m'
        · -- `m'` held `w` and was rejected for `m`
          rw [hx] at hνk
          rw [vget_congr _ hx] at hold hrej
          simp only [hhold, ↓reduceIte] at hrej
          rcases hcases with ⟨hn0, -⟩ | ⟨y, hy, hl, hn⟩ | ⟨y, hy, -, hn⟩
          · rw [hn0] at hold; cases hold
          · have hyy : y = m' := Option.some_injective _ (hy.symm.trans hold)
            have hνm : ν m ≠ w := fun e => hm' (ν.injective (hνk.trans e.symm))
            have hb := le_rank_of_rejected hI hν m (b := s.next[m]) le_rfl fun k'' _ => hfree _
            have hne : ((mp m).symm (ν m)).val ≠ s.next[m] := fun e => hνm (by
              have hj' : (mp m).symm (ν m) = j := Fin.ext e
              rw [hw, ← hj']; simp)
            have h1 : (mp m).symm w < (mp m).symm (ν m) := by
              rw [hw, Equiv.symm_apply_apply]
              exact Fin.lt_def.2 (lt_of_le_of_ne hb (Ne.symm hne))
            have h2 : (wp w).symm m < (wp w).symm (ν.symm w) := by
              rw [show ν.symm w = y from by rw [hyy, ← hνk]; simp]
              exact hl
            exact not_blocking hν h1 h2
          · have hyy : y = m' := Option.some_injective _ (hy.symm.trans hold)
            rw [hyy] at hn
            exact hrej hn
        · exact hI.opt m' k hk' hold ν hν hνk
    · have hk' : k.val < s.next[m'] := by
        rw [hnext] at hk
        split_ifs at hk with e
        · subst e
          refine hkj k hk fun e' => hx ?_
          rw [hw, hj]
          exact congrArg _ (Fin.ext e')
        · exact hk
      simp only [hhold, hx, ↓reduceIte] at hrej
      exact hI.opt m' k hk' hrej ν hν hνk

/-! ## Termination within `n²` proposals -/

/-- **Remaining proposals.** For a state $s$ of deferred acceptance with $n$ proposers and $n$
receivers, in which each proposer $m$ has made $k_m$ proposals, the number of proposals still
available is $\sum_{m} \max(n - k_m, 0)$, the sum running over all $n$ proposers. -/
def remaining (s : State n) : ℕ := ∑ m : Fin n, (n - s.next[m])

theorem remaining_init : remaining (init n) = n * n := by
  simp [remaining, init]

/-- **A proposal adds one to the proposal count.** Fix rankings for $n$ proposers and $n$
receivers. If proposer $m$ has made fewer than $n$ proposals in a state $s$ of deferred
acceptance, then after $m$ proposes, the total number of proposals made by all proposers is one
more than in $s$. -/
theorem sum_next_propose {s : State n} {m : Fin n} (h : s.next[m] < n) :
    ∑ m' : Fin n, (propose mp wp s m).next[m'] = ∑ m' : Fin n, s.next[m'] + 1 := by
  simp only [next_propose h]
  have hx : ∀ x : Fin n, (if x = m then s.next[m] + 1 else s.next[x]) =
      s.next[x] + if x = m then 1 else 0 := by
    intro x
    split_ifs with e
    · subst e; rfl
    · rfl
  simp only [hx, Finset.sum_add_distrib, Fintype.sum_ite_eq']

theorem remaining_propose_lt {s : State n} {m : Fin n} (h : s.next[m] < n) :
    remaining (propose mp wp s m) < remaining s := by
  refine Finset.sum_lt_sum (fun m' _ => ?_) ⟨m, Finset.mem_univ m, ?_⟩
  · rw [next_propose h]
    split_ifs with e
    · subst e; omega
    · omega
  · simp only [next_propose h, ↓reduceIte]
    omega

theorem run_spec : ∀ (fuel : ℕ) (s : State n), Inv mp wp s → remaining s ≤ fuel →
    Inv mp wp (run mp wp fuel s) ∧ chooser (run mp wp fuel s) = none
  | 0, s, hI, hr => by
      simp only [run]
      refine ⟨hI, List.find?_eq_none.2 fun m _ => ?_⟩
      have h0 := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hr)) m (Finset.mem_univ m)
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
      intro _
      omega
  | fuel + 1, s, hI, hr => by
      simp only [run]
      cases hc : chooser s with
      | none => exact ⟨hI, hc⟩
      | some m =>
          obtain ⟨hfree, hlt⟩ := chooser_some hc
          exact run_spec fuel _ (inv_propose hI hfree hlt)
            (by have := remaining_propose_lt (mp := mp) (wp := wp) hlt; omega)

variable (mp wp) in
theorem galeShapley_spec :
    Inv mp wp (galeShapley mp wp) ∧ chooser (galeShapley mp wp) = none :=
  run_spec _ _ inv_init (by rw [remaining_init])

variable (mp wp) in
/-- **Deferred acceptance makes at most n² proposals.** For any rankings of the $n$ receivers by
each of the $n$ proposers and of the proposers by each receiver, in the final state of deferred
acceptance the numbers of proposals made by the proposers sum to at most $n \cdot n$.

No proposer proposes more than $n$ times. -/
theorem sum_next_galeShapley_le : ∑ m : Fin n, (galeShapley mp wp).next[m] ≤ n * n := by
  calc ∑ m : Fin n, (galeShapley mp wp).next[m] ≤ ∑ _m : Fin n, n :=
        Finset.sum_le_sum fun m _ => (galeShapley_spec mp wp).1.next_le m
    _ = n * n := by simp

/-! ## The output is a perfect matching -/

/-- **When deferred acceptance stops, every proposer is held.** Fix rankings of the $n$ receivers
by each of $n$ proposers and of the proposers by each receiver. Let $s$ be a state of deferred
acceptance that satisfies the invariant of deferred acceptance for these rankings, and suppose
that no proposer is both free in $s$ and has made fewer than $n$ proposals in $s$. Then every
proposer is held by some receiver in $s$. -/
theorem held_of_done {s : State n} (hI : Inv mp wp s) (hc : chooser s = none) (m : Fin n) :
    ∃ w : Fin n, s.holder[w] = some m := by
  by_contra hno
  push Not at hno
  have hfree : Free s m := hno
  have hn : s.next[m] = n := by
    have := chooser_none hc m
    have := hI.next_le m
    have : ¬ s.next[m] < n := fun hlt => (chooser_none hc m) ⟨hfree, hlt⟩
    omega
  -- every receiver is held, by someone other than `m`
  have hw : ∀ w : Fin n, ∃ y, s.holder[w] = some y := by
    intro w
    obtain ⟨y, hy, -⟩ := hI.held m ((mp m).symm w) (by rw [hn]; exact Fin.isLt _)
    exact ⟨y, by simpa using hy⟩
  choose g hg using hw
  have hinj : Function.Injective g := fun w w' e => hI.inj w w' (g w) (hg w) (e ▸ hg w')
  have hsub : Finset.univ.image g ⊆ Finset.univ.erase m := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_erase.2 ⟨fun e => hfree w (e ▸ hg w), Finset.mem_univ _⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ m),
    Finset.card_univ, Fintype.card_fin] at this
  have : 0 < n := Fin.pos m
  omega

/-- **Every receiver holds someone once every proposer is held.** Let $s$ be a state of deferred
acceptance with $n$ proposers and $n$ receivers. If every proposer is held by some receiver in
$s$, then every receiver holds some proposer in $s$. -/
theorem holds_of_held {s : State n}
    (hall : ∀ m : Fin n, ∃ w : Fin n, s.holder[w] = some m)
    (w : Fin n) : ∃ m, s.holder[w] = some m := by
  choose f hf using hall
  have hinj : Function.Injective f := fun m m' e => by
    have h1 := hf m
    rw [e, hf m'] at h1
    exact (Option.some_injective _ h1).symm
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.1 hinj) w
  exact ⟨m, hm ▸ hf m⟩

/-- **Receiver's partner.** In a state $s$ of deferred acceptance with $n$ proposers and $n$
receivers, both numbered $0, \dots, n-1$, the partner of a receiver $w$ is the proposer she holds
in $s$; if she holds nobody, it is the proposer numbered $w$ (a default value). -/
def partnerW (s : State n) (w : Fin n) : Fin n := s.holder[w].getD w

/-- **Proposer's partner.** In a state $s$ of deferred acceptance with $n$ proposers and $n$
receivers, both numbered $0, \dots, n-1$, the partner of a proposer $m$ is the lowest-numbered
receiver that holds $m$ in $s$; if no receiver holds $m$, it is the receiver numbered $m$
(a default value). -/
def partnerM (s : State n) (m : Fin n) : Fin n :=
  ((List.finRange n).find? fun w : Fin n => s.holder[w] == some m).getD m

theorem partnerW_eq {s : State n} {w m : Fin n} (h : s.holder[w] = some m) : partnerW s w = m := by
  simp [partnerW, h]

theorem partnerM_eq {s : State n} (hI : Inv mp wp s) {w m : Fin n} (h : s.holder[w] = some m) :
    partnerM s m = w := by
  unfold partnerM
  cases hf : (List.finRange n).find? (fun w : Fin n => s.holder[w] == some m) with
  | none =>
      have := List.find?_eq_none.1 hf w (List.mem_finRange w)
      simp [h] at this
  | some w' =>
      have := List.find?_some hf
      simp only [beq_iff_eq] at this
      exact hI.inj _ _ _ this h

variable (mp wp) in
/-- **The Gale-Shapley matching**: each proposer with the receiver who holds him at the end. -/
def gsMatching : PerfectMatching (Fin n) (Fin n) where
  toFun := partnerM (galeShapley mp wp)
  invFun := partnerW (galeShapley mp wp)
  left_inv m := by
    obtain ⟨hI, hc⟩ := galeShapley_spec mp wp
    obtain ⟨w, hw⟩ := held_of_done hI hc m
    rw [partnerM_eq hI hw, partnerW_eq hw]
  right_inv w := by
    obtain ⟨hI, hc⟩ := galeShapley_spec mp wp
    obtain ⟨m, hm⟩ := holds_of_held (held_of_done hI hc) w
    rw [partnerW_eq hm, partnerM_eq hI hm]

theorem holder_gsMatching (m : Fin n) :
    (galeShapley mp wp).holder[gsMatching mp wp m] = some m := by
  obtain ⟨hI, hc⟩ := galeShapley_spec mp wp
  obtain ⟨w, hw⟩ := held_of_done hI hc m
  change (galeShapley mp wp).holder[partnerM (galeShapley mp wp) m] = some m
  rw [vget_congr _ (partnerM_eq hI hw)]
  exact hw

theorem gsMatching_symm_apply (w : Fin n) :
    (gsMatching mp wp).symm w = partnerW (galeShapley mp wp) w := rfl

/-! ## Stability and optimality -/

/-- **A proposer's final partner is his last proposal.** Let each proposer $m$ rank the $n$
receivers by a permutation $\sigma_m$ of $\{0, \dots, n-1\}$, where $\sigma_m(k)$ is his choice
of rank $k$, let each receiver rank the $n$ proposers, and let $p_m$ be the number of proposals
$m$ has made in the final state of deferred acceptance. Then $p_m \ge 1$, and the Gale-Shapley
partner $\mu(m)$ of $m$ has rank $p_m - 1$ in his ranking, that is,
$\sigma_m^{-1}(\mu(m)) = p_m - 1$. -/
theorem exists_rank_gsMatching (m : Fin n) : ∃ k : Fin n,
    k.val + 1 = (galeShapley mp wp).next[m] ∧ (mp m).symm (gsMatching mp wp m) = k := by
  obtain ⟨k, hk, hkw⟩ := (galeShapley_spec mp wp).1.last _ m (holder_gsMatching m)
  exact ⟨k, hk, by rw [← hkw]; simp⟩

variable (mp wp) in
/-- **The Gale-Shapley matching is stable.** For $n$ proposers and $n$ receivers, each with a
ranking of the other side, the perfect matching computed by deferred acceptance is stable for the
strict preferences given by these rankings. -/
theorem isStable_gsMatching : IsStable (mprefs mp) (wprefs wp) (gsMatching mp wp) := by
  intro m w hb
  obtain ⟨h1, h2⟩ := hb
  change (mp m).symm w < (mp m).symm (gsMatching mp wp m) at h1
  change (wp w).symm m < (wp w).symm ((gsMatching mp wp).symm w) at h2
  obtain ⟨k, hk, hkr⟩ := exists_rank_gsMatching (mp := mp) (wp := wp) m
  rw [hkr] at h1
  obtain ⟨y, hy, hle⟩ := (galeShapley_spec mp wp).1.held m ((mp m).symm w)
    (by have := Fin.lt_def.1 h1; omega)
  simp only [Equiv.apply_symm_apply] at hy hle
  rw [gsMatching_symm_apply, partnerW_eq hy] at h2
  exact absurd hle (not_le.2 h2)

variable (mp wp) in
/-- **Proposer-optimality**: no stable matching gives a proposer a partner he prefers to his
Gale-Shapley partner. -/
theorem gsMatching_proposer_optimal {ν : PerfectMatching (Fin n) (Fin n)}
    (hν : IsStable (mprefs mp) (wprefs wp) ν) (m : Fin n) :
    ¬ (mprefs mp m).lt (ν m) (gsMatching mp wp m) := by
  change ¬ (mp m).symm (ν m) < (mp m).symm (gsMatching mp wp m)
  obtain ⟨hI, -⟩ := galeShapley_spec mp wp
  obtain ⟨k, hk, hkr⟩ := exists_rank_gsMatching (mp := mp) (wp := wp) m
  rw [hkr, not_lt, Fin.le_def]
  refine le_rank_of_rejected hI hν m (by omega) fun k' hk' e => ?_
  have := hI.inj _ _ _ e (holder_gsMatching m)
  rw [← (mp m).apply_symm_apply (gsMatching mp wp m), hkr] at this
  have := congrArg Fin.val ((mp m).injective this)
  omega

variable (mp wp) in
/-- **Receiver-pessimality**: no stable matching gives a receiver a partner she likes less than
her Gale-Shapley partner. -/
theorem gsMatching_receiver_pessimal {ν : PerfectMatching (Fin n) (Fin n)}
    (hν : IsStable (mprefs mp) (wprefs wp) ν) (w : Fin n) :
    ¬ (wprefs wp w).lt ((gsMatching mp wp).symm w) (ν.symm w) := by
  change ¬ (wp w).symm ((gsMatching mp wp).symm w) < (wp w).symm (ν.symm w)
  intro hlt
  set m := (gsMatching mp wp).symm w with hm
  have hμm : gsMatching mp wp m = w := by simp [hm]
  have hνm : ν m ≠ w := fun e => by
    rw [show ν.symm w = m from by rw [← e]; simp] at hlt
    exact lt_irrefl _ hlt
  have hopt := gsMatching_proposer_optimal mp wp hν m
  change ¬ (mp m).symm (ν m) < (mp m).symm (gsMatching mp wp m) at hopt
  rw [hμm] at hopt
  have h1 : (mp m).symm w < (mp m).symm (ν m) :=
    lt_of_le_of_ne (not_lt.1 hopt) fun e => hνm ((mp m).symm.injective e).symm
  exact not_blocking hν h1 hlt

/-! ## Every MathlibExt preference on `Fin n` is a ranking -/

/-- **Rank under a strict total order.** For a strict total order $<$ on $\{0, \dots, n-1\}$, the
rank of an element $a$ is the number of elements $b$ with $b < a$ (the elements preferred to $a$),
as an element of $\{0, \dots, n-1\}$. -/
def orderRank (T : MathlibExt.Order.StrictTotalOrder (Fin n)) [DecidableRel T.lt] (a : Fin n) :
    Fin n :=
  ⟨(Finset.univ.filter fun b => T.lt b a).card, by
    calc (Finset.univ.filter fun b => T.lt b a).card < (Finset.univ : Finset (Fin n)).card :=
          Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => T.irrefl a
            (Finset.mem_filter.1 (h (Finset.mem_univ a))).2⟩
      _ = n := Finset.card_fin n⟩

theorem orderRank_lt {T : MathlibExt.Order.StrictTotalOrder (Fin n)} [DecidableRel T.lt]
    {a b : Fin n}
    (h : T.lt a b) : orderRank T a < orderRank T b := by
  change (Finset.univ.filter fun c => T.lt c a).card < (Finset.univ.filter fun c => T.lt c b).card
  refine Finset.card_lt_card ⟨fun c hc => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact T.trans hc h
  · exact T.irrefl a (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨Finset.mem_univ a, h⟩))).2

theorem orderRank_lt_iff {T : MathlibExt.Order.StrictTotalOrder (Fin n)} [DecidableRel T.lt]
    {a b : Fin n} :
    orderRank T a < orderRank T b ↔ T.lt a b := by
  refine ⟨fun h => ?_, orderRank_lt⟩
  rcases eq_or_ne a b with rfl | hne
  · exact absurd h (lt_irrefl _)
  · exact (T.total hne).resolve_right fun hba => absurd h (not_lt.2 (orderRank_lt hba).le)

/-- **Every strict total order on $\{0, \dots, n-1\}$ is given by a ranking.** For every strict
total order $\prec$ on $\{0, \dots, n-1\}$ there is a permutation $\sigma$ of $\{0, \dots, n-1\}$
such that, for all $a$ and $b$, $a \prec b$ holds exactly when $\sigma^{-1}(a) < \sigma^{-1}(b)$.

Hence the Gale-Shapley algorithm on rankings applies to every preference on $\{0, \dots, n-1\}$. -/
theorem exists_toOrder_eq (T : MathlibExt.Order.StrictTotalOrder (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), toOrder σ = T := by
  classical
  have hinj : Function.Injective (orderRank T) := fun a b h => by
    by_contra hne
    rcases T.total hne with hab | hba
    · exact absurd h (orderRank_lt hab).ne
    · exact absurd h (orderRank_lt hba).ne'
  let ρ := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
  refine ⟨ρ.symm, MathlibExt.Order.StrictTotalOrder.ext ?_⟩
  funext a b
  apply propext
  change ρ.symm.symm a < ρ.symm.symm b ↔ T.lt a b
  simp only [Equiv.symm_symm]
  exact orderRank_lt_iff

/-- **Gale-Shapley serves every preference profile with $n$ proposers and $n$ receivers.** Let
the $n$ proposers and the $n$ receivers both be numbered $0, \dots, n-1$. Let each proposer $m$
have a strict total order $<_m$ of preference on the receivers and each receiver $w$ a strict
total order $<_w$ of preference on the proposers, where $x <_m y$ means that $m$ prefers $x$ to
$y$, and likewise for $<_w$. Then there are permutations $\sigma_m$ (one for each proposer $m$)
and $\tau_w$ (one for each receiver $w$) of $\{0, \dots, n-1\}$, read as rankings, such that
$w <_m w'$ exactly when $\sigma_m^{-1}(w) < \sigma_m^{-1}(w')$ and $a <_w b$ exactly when
$\tau_w^{-1}(a) < \tau_w^{-1}(b)$, and the Gale-Shapley matching $\mu$ of the rankings $\sigma$
and $\tau$ is stable for these preferences and proposer-optimal: for every perfect matching $\nu$
that is stable for these preferences and every proposer $m$, it is not the case that
$\nu(m) <_m \mu(m)$. -/
theorem exists_rankings_gsMatching (mp' : MPrefs (Fin n) (Fin n)) (wp' : WPrefs (Fin n) (Fin n)) :
    ∃ σ τ : Fin n → Equiv.Perm (Fin n), mprefs σ = mp' ∧ wprefs τ = wp' ∧
      IsStable mp' wp' (gsMatching σ τ) ∧
      ∀ ν : PerfectMatching (Fin n) (Fin n), IsStable mp' wp' ν →
        ∀ m, ¬ (mp' m).lt (ν m) (gsMatching σ τ m) := by
  choose σ hσ using fun m => exists_toOrder_eq (mp' m)
  choose τ hτ using fun w => exists_toOrder_eq (wp' w)
  have hm : mprefs σ = mp' := funext hσ
  have hw : wprefs τ = wp' := funext hτ
  refine ⟨σ, τ, hm, hw, hm ▸ hw ▸ isStable_gsMatching σ τ, fun ν hν m => ?_⟩
  subst hm hw
  exact gsMatching_proposer_optimal σ τ hν m

end Cslib.Algorithms.Lean.Matching.GaleShapley
