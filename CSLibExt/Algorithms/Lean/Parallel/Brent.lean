/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The work-span model and Brent's theorem

A parallel computation is a DAG of unit-time tasks (`Dag`, numbered in a topological order). Its
*work* is the number of tasks `n` and its *span* the number of tasks on a longest path
(`depth`, `span`). A *schedule* on `p` processors runs each task in one step, after its
predecessors, with at most `p` tasks per step (`Schedule`).

Main results (Brent, *The parallel evaluation of general arithmetic expressions*, J. ACM 21,
1974; CLRS, third edition, Section 27.1, the work law, the span law, and the bound
`T_P ≤ T_1 / P + T_∞`):

* `Schedule.work_le` (**work law**): every schedule takes at least `n / p` steps,
  `n ≤ p * length`.
* `Schedule.span_le` (**span law**): every schedule takes at least `span` steps.
* `levelSchedule`, `levelSchedule_length` (**Brent's theorem**): scheduling level by level, each
  level of `L` tasks in `⌈L / p⌉` steps, takes `T` steps with `p T ≤ n + (p - 1) D`, that is
  `T ≤ (n - D) / p + D ≤ n / p + D`; `brent` packages it with the two laws, so the optimal
  length is within a factor `2` of `max (n / p) D`.

The schedule here is Brent's level-by-level one; the theorem that *every* greedy scheduler meets
the same bound (CLRS Theorem 27.1) is not formalized.

## Cost model

Work-span: tasks take unit time and processors are identical; communication and scheduling
overhead are free. `depth` is a specification (evaluated directly it recomputes shared subpaths,
exponentially many on some DAGs); `depthTable` computes each depth once, in topological order,
in polynomial time (`O(n² + n |E|)` with lists), and is proved equal (`getD_depthTable`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Parallel.Brent

/-- **Computation DAG.** A computation DAG on $n$ unit-time tasks, numbered $0, \dots, n - 1$,
assigns to each task $v$ a list of predecessors (the tasks $v$ waits for), each numbered below
$v$; so the numbering is a topological order. -/
structure Dag (n : ℕ) where
  /-- The tasks each task waits for. -/
  preds : Fin n → List (Fin n)
  /-- Predecessors come first. -/
  topo : ∀ v, ∀ u ∈ preds v, u < v

variable {n : ℕ} (G : Dag n)

/-- **Depth of a task in a computation DAG.** The depth of a task $v$ is the number of tasks on a
longest path ending at $v$: it is $1$ plus the largest depth of a predecessor of $v$, or $1$ if
$v$ has no predecessors. -/
def depth (v : Fin n) : ℕ :=
  1 + ((G.preds v).attach.map fun u => depth u.1).foldr max 0
termination_by v.val
decreasing_by exact G.topo v u.1 u.2

/-- **Span of a computation DAG.** The span of a computation DAG is the number of tasks on a
longest path, that is, the largest depth of a task, and $0$ when there are no tasks. -/
def span : ℕ := Finset.univ.sup (depth G)

private theorem le_foldr_max {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.foldr max 0
  | b :: _, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (le_foldr_max h).trans (Nat.le_max_right _ _)

private theorem foldr_max_le {B : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a ≤ B) → l.foldr max 0 ≤ B
  | [], _ => Nat.zero_le _
  | b :: _, h => Nat.max_le.2 ⟨h b List.mem_cons_self,
      foldr_max_le fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

theorem one_le_depth (v : Fin n) : 1 ≤ depth G v := by
  rw [depth]; omega

/-- **Predecessors have smaller depth.** In a computation DAG, if $u$ is a predecessor of $v$,
then the depth of $u$ is strictly less than the depth of $v$. -/
theorem depth_lt_of_mem {u v : Fin n} (hu : u ∈ G.preds v) : depth G u < depth G v := by
  conv_rhs => rw [depth]
  have : depth G u ≤ ((G.preds v).attach.map fun u => depth G u.1).foldr max 0 :=
    le_foldr_max (List.mem_map.2 ⟨⟨u, hu⟩, List.mem_attach _ _, rfl⟩)
  omega

theorem depth_le_span (v : Fin n) : depth G v ≤ span G :=
  Finset.le_sup (f := depth G) (Finset.mem_univ v)

/-! ## Tabulated depths -/

/-- **Depths of an initial segment of tasks.** For $k \le n$, the list of the depths of tasks
$0, \dots, k - 1$ of a computation DAG on $n$ tasks, computed in topological order: the empty
list for $k = 0$, and for $k + 1$ the list for $k$ followed by $1$ plus the largest entry of that
list at a predecessor of task $k$ (or $1$ if task $k$ has no predecessors). -/
def depthsUpTo : (k : ℕ) → k ≤ n → List ℕ
  | 0, _ => []
  | k + 1, h =>
      let acc := depthsUpTo k (Nat.le_of_succ_le h)
      acc ++ [1 + ((G.preds ⟨k, h⟩).map fun u => acc.getD u.val 0).foldr max 0]

/-- **Table of depths.** The list of the depths of tasks $0, \dots, n - 1$ of a computation DAG on
$n$ tasks, computed once each in topological order: the entry for task $k$ is $1$ plus the largest
entry at a predecessor of $k$, or $1$ if $k$ has no predecessors.

With lists (appending and indexed reads take linear time) this costs $O(n^2 + n|E|)$, where $|E|$
is the total number of predecessor entries; evaluating the depth directly from its recursive
definition instead recomputes shared subpaths exponentially often. -/
def depthTable : List ℕ := depthsUpTo G n (Nat.le_refl n)

theorem length_depthsUpTo : ∀ (k : ℕ) (h : k ≤ n), (depthsUpTo G k h).length = k
  | 0, _ => rfl
  | k + 1, h => by simp [depthsUpTo, length_depthsUpTo k]

theorem getD_depthsUpTo : ∀ (k : ℕ) (h : k ≤ n) (i : ℕ) (hi : i < k),
    (depthsUpTo G k h).getD i 0 = depth G ⟨i, by omega⟩
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, h, i, hi => by
      have hl := length_depthsUpTo G k (Nat.le_of_succ_le h)
      simp only [depthsUpTo]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
        exact getD_depthsUpTo k _ i hi
      · rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self]
        simp only [List.getD_cons_zero]
        conv_rhs => rw [depth]
        congr 2
        rw [show (fun u : {x // x ∈ G.preds ⟨i, h⟩} => depth G u.1) = depth G ∘ Subtype.val
          from rfl, ← List.map_map, List.attach_map_subtype_val]
        refine List.map_congr_left fun u hu => ?_
        exact getD_depthsUpTo i _ u.val (G.topo _ u hu)

/-- **The table of depths is correct.** For every task $v$ of a computation DAG, the entry of the
table of depths at position $v$ equals the depth of $v$. -/
theorem getD_depthTable (v : Fin n) : (depthTable G).getD v.val 0 = depth G v :=
  getD_depthsUpTo G n _ v.val v.isLt

/-! ## Schedules -/

/-- **Schedule of a computation DAG.** A schedule of a computation DAG on $n$ tasks on $p$
processors assigns to each task $v$ a step $t(v) \in \mathbb{N}$ in which it runs, such that
$t(u) < t(v)$ whenever $u$ is a predecessor of $v$, and for every step $s$ at most $p$ tasks $v$
have $t(v) = s$. -/
structure Schedule (p : ℕ) where
  /-- The step in which each task runs. -/
  time : Fin n → ℕ
  /-- Predecessors run earlier. -/
  prec : ∀ v, ∀ u ∈ G.preds v, time u < time v
  /-- At most `p` tasks per step. -/
  cap : ∀ t, (Finset.univ.filter fun v => time v = t).card ≤ p

variable {G}

/-- **Length of a schedule.** The length of a schedule is the number of steps it takes: one more
than the latest step in which a task runs (steps are numbered from $0$), or $0$ if there are no
tasks. -/
def Schedule.length {p : ℕ} (S : Schedule G p) : ℕ := Finset.univ.sup fun v => S.time v + 1

theorem Schedule.time_lt_length {p : ℕ} (S : Schedule G p) (v : Fin n) : S.time v < S.length :=
  Finset.le_sup (f := fun v => S.time v + 1) (Finset.mem_univ v)

/-- **The work law.** For a computation DAG on $n$ tasks, every schedule of it on $p$ processors
that takes $T$ steps satisfies $n \le p T$. In particular, for $p > 0$ the schedule takes at
least $n / p$ steps. -/
theorem Schedule.work_le {p : ℕ} (S : Schedule G p) : n ≤ p * S.length := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.range S.length)
    (f := S.time) fun v _ => Finset.mem_range.2 (S.time_lt_length v)
  rw [Finset.card_univ, Fintype.card_fin] at h
  calc n = ∑ t ∈ Finset.range S.length, (Finset.univ.filter fun v => S.time v = t).card := h
    _ ≤ ∑ _t ∈ Finset.range S.length, p := Finset.sum_le_sum fun t _ => S.cap t
    _ = p * S.length := by rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range,
        Nat.mul_comm]

/-- **Depth bounds the step of a task.** For every schedule of a computation DAG on $p$
processors, with steps numbered from $0$, every task $v$ runs in a step $t$ with
$\operatorname{depth}(v) \le t + 1$. -/
theorem Schedule.depth_le_time {p : ℕ} (S : Schedule G p) (v : Fin n) :
    depth G v ≤ S.time v + 1 := by
  have : ((G.preds v).attach.map fun u => depth G u.1).foldr max 0 ≤ S.time v :=
    foldr_max_le fun a ha => by
      obtain ⟨⟨u, hu⟩, _, rfl⟩ := List.mem_map.1 ha
      dsimp only
      have h1 := S.depth_le_time u
      have h2 := S.prec v u hu
      omega
  rw [depth]
  omega
termination_by v.val
decreasing_by exact G.topo v u hu

/-- **The span law**: no schedule is shorter than the span. -/
theorem Schedule.span_le {p : ℕ} (S : Schedule G p) : span G ≤ S.length :=
  Finset.sup_le fun v _ => (S.depth_le_time v).trans (S.time_lt_length v)

/-! ## Brent's level-by-level schedule -/

variable (G)

/-- **Level size.** For a computation DAG and a natural number $d$, the size of level $d$ is the
number of tasks of depth $d$. -/
def levelCard (d : ℕ) : ℕ := (Finset.univ.filter fun v => depth G v = d).card

/-- **Steps of a level.** For a computation DAG and natural numbers $p$ and $d$, let $L_d$ be the
number of tasks of depth $d$. The number of steps of level $d$ on $p$ processors is
$\lceil L_d / p \rceil$ if $p \ge 1$, and $0$ if $p = 0$. -/
def levelSteps (p d : ℕ) : ℕ := (levelCard G d + p - 1) / p

/-- **First step of a level.** For a computation DAG and natural numbers $p$ and $d$, let $s_e$
be the number of steps of level $e$ on $p$ processors: $\lceil L_e / p \rceil$ if $p \ge 1$ and
$0$ if $p = 0$, where $L_e$ is the number of tasks of depth $e$. The first step of level $d$ is
$\sum_{e < d} s_e$. -/
def offset (p d : ℕ) : ℕ := ∑ e ∈ Finset.range d, levelSteps G p e

/-- **Rank within a level.** In a computation DAG, the rank of a task $v$ is the number of tasks
of the same depth as $v$ with a smaller number than $v$. Taken in numbering order, the tasks of a
level have ranks $0, 1, 2, \dots$ -/
def rank (v : Fin n) : ℕ := (Finset.univ.filter fun u => depth G u = depth G v ∧ u < v).card

/-- **Step of a task in Brent's schedule.** Let $G$ be a computation DAG and $p$ a natural number.
If $p \ge 1$, for each $d$ let $L_d$ be the number of tasks of depth $d$ and
$o_d = \sum_{e < d} \lceil L_e / p \rceil$, and for each task $v$ let $r(v)$ be the number of tasks
of the same depth as $v$ with a smaller number; the step of a task $v$ is
$o_{\operatorname{depth}(v)} + \lfloor r(v) / p \rfloor$. If $p = 0$, the step of every task is $0$.

For $p \ge 1$ this runs the tasks level by level, each level of $L_d$ tasks in
$\lceil L_d / p \rceil$ steps of at most $p$ tasks. -/
def levelTime (p : ℕ) (v : Fin n) : ℕ := offset G p (depth G v) + rank G v / p

theorem rank_lt_levelCard (v : Fin n) : rank G v < levelCard G (depth G v) := by
  apply Finset.card_lt_card
  refine ⟨fun u hu => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1
  · have := h (Finset.mem_filter.2 ⟨Finset.mem_univ v, rfl⟩)
    simp at this

theorem rank_div_lt {p : ℕ} (hp : 1 ≤ p) (v : Fin n) :
    rank G v / p < levelSteps G p (depth G v) := by
  have h := rank_lt_levelCard G v
  unfold levelSteps
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have h1 := Nat.div_add_mod (levelCard G (depth G v) + p - 1) p
  have h2 := Nat.mod_lt (levelCard G (depth G v) + p - 1) (show 0 < p by omega)
  rw [Nat.mul_comm] at h1
  generalize (levelCard G (depth G v) + p - 1) / p * p = m at *
  omega

theorem offset_add_le {p d e : ℕ} (h : d < e) : offset G p d + levelSteps G p d ≤ offset G p e := by
  unfold offset
  rw [← Finset.sum_range_succ]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

theorem levelTime_lt {p : ℕ} (hp : 1 ≤ p) (v : Fin n) :
    levelTime G p v < offset G p (depth G v) + levelSteps G p (depth G v) := by
  have := rank_div_lt G hp v
  unfold levelTime
  omega

/-- **No step of Brent's level schedule mixes levels.** Let $G$ be a computation DAG and
$p \ge 1$. If two tasks $u$ and $v$ run in the same step of Brent's level-by-level schedule on
$p$ processors, then $u$ and $v$ have the same depth. -/
theorem depth_eq_of_levelTime_eq {p : ℕ} (hp : 1 ≤ p) {u v : Fin n}
    (h : levelTime G p u = levelTime G p v) : depth G u = depth G v := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := levelTime_lt G hp u
    have h2 := offset_add_le G (p := p) hlt
    have h3 : offset G p (depth G v) ≤ levelTime G p v := Nat.le_add_right _ _
    omega
  · have h1 := levelTime_lt G hp v
    have h2 := offset_add_le G (p := p) hlt
    have h3 : offset G p (depth G u) ≤ levelTime G p u := Nat.le_add_right _ _
    omega

/-- **Ranks increase within a level.** In a computation DAG, if tasks $u$ and $v$ have the same
depth and $u$ has a smaller number than $v$, then the rank of $u$ is smaller than the rank of
$v$, where the rank of a task is the number of tasks of the same depth with a smaller number.
In particular, ranks are distinct within a level. -/
theorem rank_lt_rank {u v : Fin n} (hd : depth G u = depth G v) (h : u < v) :
    rank G u < rank G v := by
  apply Finset.card_lt_card
  refine ⟨fun w hw => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨hw.1.trans hd, hw.2.trans h⟩
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ u, hd, h⟩)
    simp at this

/-- **Brent's level schedule.** Let $G$ be a computation DAG and $p \ge 1$. For each $d$ let
$L_d$ be the number of tasks of depth $d$ and $o_d = \sum_{e < d} \lceil L_e / p \rceil$, and for
each task $v$ let $r(v)$ be the number of tasks of the same depth as $v$ with a smaller number.
Brent's level schedule is the schedule of $G$ on $p$ processors that runs each task $v$ at step
$o_{\operatorname{depth}(v)} + \lfloor r(v) / p \rfloor$.

It runs the tasks level by level, in order of depth, each level of $L_d$ tasks in
$\lceil L_d / p \rceil$ steps of at most $p$ tasks. -/
def levelSchedule {p : ℕ} (hp : 1 ≤ p) : Schedule G p where
  time := levelTime G p
  prec v u hu := by
    have hlt := depth_lt_of_mem G hu
    have h1 := levelTime_lt G hp u
    have h2 := offset_add_le G (p := p) hlt
    have h3 : offset G p (depth G v) ≤ levelTime G p v := Nat.le_add_right _ _
    omega
  cap t := by
    by_cases hne : (Finset.univ.filter fun v => levelTime G p v = t).Nonempty
    · obtain ⟨w, hw⟩ := hne
      have hwt : levelTime G p w = t := (Finset.mem_filter.1 hw).2
      set j := rank G w / p
      -- every task in step `t` has rank in `[j p, j p + p)`
      have hmaps : ∀ v ∈ Finset.univ.filter (fun v => levelTime G p v = t),
          rank G v ∈ Finset.Ico (j * p) (j * p + p) := fun v hv => by
        have hvt : levelTime G p v = t := (Finset.mem_filter.1 hv).2
        have hd := depth_eq_of_levelTime_eq G hp (hvt.trans hwt.symm)
        have hj : rank G v / p = j := by
          have := hvt.trans hwt.symm
          unfold levelTime at this
          rw [hd] at this
          omega
        rw [Finset.mem_Ico]
        constructor
        · rw [← hj]; exact Nat.div_mul_le_self _ _
        · rw [← hj]
          have := Nat.lt_div_mul_add (a := rank G v) (show 0 < p by omega)
          omega
      have hinj : Set.InjOn (rank G) (Finset.univ.filter fun v => levelTime G p v = t) :=
        fun u hu v hv huv => by
          have hd := depth_eq_of_levelTime_eq G hp
            ((Finset.mem_filter.1 hu).2.trans (Finset.mem_filter.1 hv).2.symm)
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact absurd huv (Nat.ne_of_lt (rank_lt_rank G hd h))
          · exact absurd huv (Nat.ne_of_gt (rank_lt_rank G hd.symm h))
      have := Finset.card_le_card_of_injOn (rank G) hmaps hinj
      rwa [Nat.card_Ico, Nat.add_sub_cancel_left] at this
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty]
      exact Nat.zero_le _

/-- **Level $0$ is empty.** In every computation DAG no task has depth $0$, so the number of
tasks of depth $0$ is $0$. -/
theorem levelCard_zero : levelCard G 0 = 0 := by
  rw [levelCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _
  have := one_le_depth G v
  omega

/-- **Brent's theorem.** Let $G$ be a computation DAG with $n$ tasks and span $D$, and let
$p \ge 1$. If Brent's level schedule of $G$ on $p$ processors takes $T$ steps, then
$pT \le n + (p - 1) D$, that is, $T \le (n - D)/p + D$. -/
theorem levelSchedule_length {p : ℕ} (hp : 1 ≤ p) :
    p * (levelSchedule G hp).length ≤ n + (p - 1) * span G := by
  set D := span G
  -- the length is at most the first step after the last level
  have hlen : (levelSchedule G hp).length ≤ offset G p (D + 1) := Finset.sup_le fun v _ => by
    have h1 := levelTime_lt G hp v
    have h2 := offset_add_le G (p := p)
      (show depth G v < D + 1 from Nat.lt_succ_of_le (depth_le_span G v))
    change levelTime G p v + 1 ≤ _
    omega
  -- `p` times the steps of each level is at most its tasks plus `p - 1`
  have hsteps : ∀ d, p * levelSteps G p d ≤ levelCard G d + (p - 1) := fun d => by
    unfold levelSteps
    have := Nat.div_mul_le_self (levelCard G d + p - 1) p
    rw [Nat.mul_comm]
    omega
  -- the levels partition the tasks
  have hsum : ∑ d ∈ Finset.range (D + 1), levelCard G d = n := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.range (D + 1))
      (f := depth G) fun v _ => Finset.mem_range.2 (Nat.lt_succ_of_le (depth_le_span G v))
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hoff : p * offset G p (D + 1) ≤ n + (p - 1) * D := by
    unfold offset
    have h0 : levelSteps G p 0 = 0 := by
      unfold levelSteps; rw [levelCard_zero]; exact Nat.div_eq_of_lt (by omega)
    rw [Finset.sum_range_succ', h0, Nat.add_zero, Finset.mul_sum]
    rw [Finset.sum_range_succ'] at hsum
    rw [levelCard_zero, Nat.add_zero] at hsum
    calc ∑ d ∈ Finset.range D, p * levelSteps G p (d + 1)
        ≤ ∑ d ∈ Finset.range D, (levelCard G (d + 1) + (p - 1)) :=
          Finset.sum_le_sum fun d _ => hsteps (d + 1)
      _ = n + (p - 1) * D := by
          rw [Finset.sum_add_distrib, hsum, Finset.sum_const_nat (fun _ _ => rfl),
            Finset.card_range, Nat.mul_comm]
  calc p * (levelSchedule G hp).length ≤ p * offset G p (D + 1) := Nat.mul_le_mul_left p hlen
    _ ≤ n + (p - 1) * D := hoff

/-- **Brent's theorem with the work and span laws.** Let $G$ be a computation DAG on $n$
unit-time tasks with span $D$, and let $p \ge 1$. Then some schedule of $G$ on $p$ processors
has length $T$ with $pT \le n + (p - 1)D$, and every schedule of $G$ on $p$ processors has a
length $T'$ with $n \le pT'$ (the work law) and $D \le T'$ (the span law). -/
theorem brent {p : ℕ} (hp : 1 ≤ p) :
    ∃ S : Schedule G p, p * S.length ≤ n + (p - 1) * span G ∧
      ∀ S' : Schedule G p, n ≤ p * S'.length ∧ span G ≤ S'.length :=
  ⟨levelSchedule G hp, levelSchedule_length G hp, fun S' => ⟨S'.work_le, S'.span_le⟩⟩

end Cslib.Algorithms.Lean.Parallel.Brent
