/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith

/-!
# Backward induction for deterministic finite-horizon control

A deterministic finite-horizon control problem (`ControlProblem N S U`) has stages
`t = 0, …, N - 1`, states in a type `S` and actions in a type `U`. At stage `t` in state `s` the
admissible actions form a nonempty finite set `A_t(s)`, an action `a` leads to the state
`F_t(s, a)` at the real cost `c_t(s, a)`, and a state reached at stage `N` costs `g`.

An admissible sequence from state `s` at stage `t` is a pair of a state sequence `x` and an action
sequence `u` with `x t = s`, `u i ∈ A_i(x i)` and `x (i + 1) = F_i(x i, u i)` for `t ≤ i < N`
(`ControlProblem.IsAdmissibleSequence`); its total cost is
`∑_{t ≤ i < N} c_i(x i, u i) + g(x N)` (`ControlProblem.totalCost`).

`ControlProblem.backward_induction` proves, for any `V` with `V_N = g` and
`V_t(s) = min_{a ∈ A_t(s)} (c_t(s, a) + V_{t+1}(F_t(s, a)))`, that `V_t(s)` is the minimum total
cost of an admissible sequence from `s` at stage `t`, that an admissible sequence choosing a
minimizing action at every stage attains it, and that `V_t(s)` is the length of a shortest path
from `(t, s)` to the sink in the stage-indexed graph. That graph is the quiver on
`ControlProblem.StageVertex` with arcs `ControlProblem.StageArc` and lengths
`ControlProblem.stageArcLength`; its paths and path lengths are Mathlib's `Quiver.Path` and
`Quiver.Path.addWeight`, and it is acyclic (`ControlProblem.stageArc_acyclic`).
`ControlProblem.backwardValue` is the solution of the recursion, computed by
`Fin.reverseInduction`.

The states need not be finite: only the admissible sets need to be finite and nonempty, so that
each minimum is attained. The stochastic, stationary and discounted analogue with all actions
available is `Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon`; its model has no admissible sets
or stage-dependent data, so it is not reused here.

## Main results

* `Cslib.Algorithms.Lean.DeterministicFiniteHorizon.ControlProblem.backward_induction`:
  the backward-induction values are the minimum total costs, minimizing choices are optimal, and
  the values are shortest-path distances to the sink.
* `Cslib.Algorithms.Lean.DeterministicFiniteHorizon.ControlProblem.stageArc_acyclic`:
  the stage-indexed graph has no cycles.

## References

* S. Ma, *Handout 4: Deterministic Systems and the Shortest Path Problem*, SEEM 3470, CUHK, 2014
  (its suggested reading: D. P. Bertsekas, *Dynamic Programming and Optimal Control*, Vol. I,
  3rd ed., Athena Scientific, 2005, §§2.1–2.2), §2.1 and the DP recursion (1).
* D. P. Bertsekas, *Lecture Slides – Dynamic Programming*, based on lectures given at MIT, Fall
  2015, Lecture 2, slide "DP algorithm" (optimality of minimizing choices), and Lecture 3, slides
  "Deterministic finite-state problem" and "Backward and forward DP algorithms" (shortest paths).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DeterministicFiniteHorizon

open Finset

universe u v

/-- **Deterministic finite-horizon control problem.** A problem with $N$ stages
$t = 0, \dots, N - 1$, states in $S$ and actions in $U$: at stage $t$ in state $s$ the admissible
actions form a nonempty finite set $A_t(s) \subseteq U$, an action $a$ leads to the state
$F_t(s, a)$ at the real cost $c_t(s, a)$, and a state $s$ reached at stage $N$ costs $g(s)$. -/
structure ControlProblem (N : ℕ) (S : Type u) (U : Type v) where
  /-- The admissible actions $A_t(s)$ at stage $t$ in state $s$. -/
  admissible : Fin N → S → Finset U
  /-- Every admissible set is nonempty. -/
  admissible_nonempty : ∀ t s, (admissible t s).Nonempty
  /-- The transition $F_t(s, a)$. -/
  transition : Fin N → S → U → S
  /-- The stage cost $c_t(s, a)$. -/
  cost : Fin N → S → U → ℝ
  /-- The terminal cost $g$. -/
  terminalCost : S → ℝ

namespace ControlProblem

variable {N : ℕ} {S : Type u} {U : Type v} (P : ControlProblem N S U)

/-- **Admissible sequence of a deterministic control problem.** States
$x_0, \dots, x_N \in S$ and actions $u_0, \dots, u_{N-1} \in U$ form an admissible sequence from
state $s$ at stage $t \le N$ when $x_t = s$ and, for every stage $i$ with $t \le i < N$,
$u_i \in A_i(x_i)$ and $x_{i+1} = F_i(x_i, u_i)$. Entries before stage $t$ are unconstrained. -/
def IsAdmissibleSequence (t : Fin (N + 1)) (s : S) (x : Fin (N + 1) → S) (u : Fin N → U) :
    Prop :=
  x t = s ∧ ∀ i : Fin N, t ≤ i.castSucc →
    u i ∈ P.admissible i (x i.castSucc) ∧ x i.succ = P.transition i (x i.castSucc) (u i)

/-- **Total cost of a control sequence from a stage.** For states $x_0, \dots, x_N$ and actions
$u_0, \dots, u_{N-1}$, the total cost from stage $t \le N$ is
$\sum_{t \le i < N} c_i(x_i, u_i) + g(x_N)$. -/
def totalCost (t : Fin (N + 1)) (x : Fin (N + 1) → S) (u : Fin N → U) : ℝ :=
  (∑ i : Fin N with t ≤ i.castSucc, P.cost i (x i.castSucc) (u i)) +
    P.terminalCost (x (Fin.last N))

/-- **Backward-induction values.** The values $V_t(s)$ of a deterministic control problem for
$t = N, N - 1, \dots, 0$: $V_N = g$ and
$V_t(s) = \min_{a \in A_t(s)} \bigl(c_t(s, a) + V_{t+1}(F_t(s, a))\bigr)$ for $t < N$. -/
noncomputable def backwardValue : Fin (N + 1) → S → ℝ :=
  Fin.reverseInduction (motive := fun _ => S → ℝ) P.terminalCost fun i V s =>
    (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
      P.cost i s a + V (P.transition i s a)

/-- **Vertices of the stage-indexed graph.** For a deterministic control problem with $N$ stages
and states in $S$, a vertex is a pair $(t, s)$ of a stage $t \in \{0, \dots, N\}$ and a state
$s \in S$, or the sink. -/
inductive StageVertex (P : ControlProblem N S U) where
  /-- The vertex $(t, s)$. -/
  | node (t : Fin (N + 1)) (s : S)
  /-- The sink. -/
  | sink

/-- **Arcs of the stage-indexed graph.** For each stage $i < N$, state $s$ and admissible action
$a \in A_i(s)$ there is an arc $(i, s) \to (i + 1, F_i(s, a))$, and for each state $s$ there is
an arc from $(N, s)$ to the sink. -/
inductive StageArc : P.StageVertex → P.StageVertex → Type (max u v) where
  /-- The arc $(i, s) \to (i + 1, F_i(s, a))$ of an admissible action $a \in A_i(s)$. -/
  | step (i : Fin N) (s : S) (a : U) (ha : a ∈ P.admissible i s) :
      StageArc (.node i.castSucc s) (.node i.succ (P.transition i s a))
  /-- The arc from $(N, s)$ to the sink. -/
  | exit (s : S) : StageArc (.node (Fin.last N) s) .sink

-- The stage-indexed graph: the quiver on `P.StageVertex` whose arrows are the arcs `P.StageArc`.
instance : Quiver.{max u v} P.StageVertex where
  Hom := P.StageArc

/-- **Arc lengths of the stage-indexed graph.** The arc $(i, s) \to (i + 1, F_i(s, a))$ of the
action $a$ has length $c_i(s, a)$, and the arc from $(N, s)$ to the sink has length $g(s)$. -/
def stageArcLength : ∀ {v w : P.StageVertex}, (v ⟶ w) → ℝ
  | _, _, .step i s a _ => P.cost i s a
  | _, _, .exit s => P.terminalCost s

@[simp]
theorem backwardValue_last : P.backwardValue (Fin.last N) = P.terminalCost := by
  simp [backwardValue]

theorem backwardValue_castSucc (i : Fin N) (s : S) :
    P.backwardValue i.castSucc s = (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
      P.cost i s a + P.backwardValue i.succ (P.transition i s a) := by
  simp [backwardValue]

@[simp]
theorem totalCost_last (x : Fin (N + 1) → S) (u : Fin N → U) :
    P.totalCost (Fin.last N) x u = P.terminalCost (x (Fin.last N)) := by
  simp [totalCost]

theorem totalCost_castSucc (i : Fin N) (x : Fin (N + 1) → S) (u : Fin N → U) :
    P.totalCost i.castSucc x u = P.cost i (x i.castSucc) (u i) + P.totalCost i.succ x u := by
  have hset : (univ.filter fun j : Fin N => i.castSucc ≤ j.castSucc) =
      insert i (univ.filter fun j : Fin N => i.succ ≤ j.castSucc) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.le_iff_val_le_val,
      Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
    omega
  have hi : i ∉ (univ.filter fun j : Fin N => i.succ ≤ j.castSucc) := by
    simp [Fin.le_iff_val_le_val]
  unfold totalCost
  rw [hset, sum_insert hi, add_assoc]

section Recursion

variable {P} {V : Fin (N + 1) → S → ℝ}

/-- No admissible sequence costs less than the values of the recursion. -/
private theorem le_totalCost (hV_last : ∀ s, V (Fin.last N) s = P.terminalCost s)
    (hV : ∀ (i : Fin N) (s : S), V i.castSucc s =
      (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
        P.cost i s a + V i.succ (P.transition i s a))
    {t : Fin (N + 1)} {s : S} {x : Fin (N + 1) → S} {u : Fin N → U}
    (h : P.IsAdmissibleSequence t s x u) : V t s ≤ P.totalCost t x u := by
  have key : ∀ t' : Fin (N + 1), t ≤ t' → V t' (x t') ≤ P.totalCost t' x u := by
    intro t'
    induction t' using Fin.reverseInduction with
    | last => intro _; rw [totalCost_last, hV_last]
    | cast i ih =>
      intro hti
      obtain ⟨hmem, hx⟩ := h.2 i hti
      have hle := ih (hti.trans (Fin.castSucc_le_succ i))
      rw [totalCost_castSucc, hV]
      calc _ ≤ P.cost i (x i.castSucc) (u i) + V i.succ (P.transition i (x i.castSucc) (u i)) :=
            inf'_le _ hmem
        _ ≤ _ := by rw [← hx]; gcongr
  simpa [h.1] using key t le_rfl

/-- An admissible sequence choosing minimizing actions costs exactly the value. -/
private theorem totalCost_eq_of_minimizing (hV_last : ∀ s, V (Fin.last N) s = P.terminalCost s)
    (hV : ∀ (i : Fin N) (s : S), V i.castSucc s =
      (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
        P.cost i s a + V i.succ (P.transition i s a))
    {t : Fin (N + 1)} {s : S} {x : Fin (N + 1) → S} {u : Fin N → U}
    (h : P.IsAdmissibleSequence t s x u)
    (hmin : ∀ i : Fin N, t ≤ i.castSucc → ∀ a ∈ P.admissible i (x i.castSucc),
      P.cost i (x i.castSucc) (u i) + V i.succ (P.transition i (x i.castSucc) (u i)) ≤
        P.cost i (x i.castSucc) a + V i.succ (P.transition i (x i.castSucc) a)) :
    P.totalCost t x u = V t s := by
  have key : ∀ t' : Fin (N + 1), t ≤ t' → P.totalCost t' x u = V t' (x t') := by
    intro t'
    induction t' using Fin.reverseInduction with
    | last => intro _; rw [totalCost_last, hV_last]
    | cast i ih =>
      intro hti
      obtain ⟨hmem, hx⟩ := h.2 i hti
      rw [totalCost_castSucc, ih (hti.trans (Fin.castSucc_le_succ i)), hx, hV]
      exact le_antisymm (le_inf' _ _ (hmin i hti)) (inf'_le _ hmem)
  simpa [h.1] using key t le_rfl

/-- Some admissible sequence choosing minimizing actions starts from every stage and state. -/
private theorem exists_minimizing (t : Fin (N + 1)) (s : S) :
    ∃ x u, P.IsAdmissibleSequence t s x u ∧
      ∀ i : Fin N, t ≤ i.castSucc → ∀ a ∈ P.admissible i (x i.castSucc),
        P.cost i (x i.castSucc) (u i) + V i.succ (P.transition i (x i.castSucc) (u i)) ≤
          P.cost i (x i.castSucc) a + V i.succ (P.transition i (x i.castSucc) a) := by
  have hsel : ∀ (i : Fin N) (y : S), ∃ b ∈ P.admissible i y, ∀ a ∈ P.admissible i y,
      P.cost i y b + V i.succ (P.transition i y b) ≤
        P.cost i y a + V i.succ (P.transition i y a) := by
    intro i y
    obtain ⟨b, hb, hbeq⟩ := exists_mem_eq_inf' (P.admissible_nonempty i y)
      fun a => P.cost i y a + V i.succ (P.transition i y a)
    exact ⟨b, hb, fun a ha => hbeq ▸ inf'_le _ ha⟩
  choose μ hμmem hμmin using hsel
  let x : Fin (N + 1) → S := Fin.induction (motive := fun _ => S) s fun j y =>
    if j.castSucc < t then s else P.transition j y (μ j y)
  have hx_before : ∀ j : Fin (N + 1), j ≤ t → x j = s := by
    intro j hj
    induction j using Fin.cases with
    | zero => simp [x]
    | succ k =>
      have hk : k.castSucc < t := Fin.castSucc_lt_iff_succ_le.mpr hj
      simp [x, hk]
  have hx_after : ∀ k : Fin N, t ≤ k.castSucc →
      x k.succ = P.transition k (x k.castSucc) (μ k (x k.castSucc)) := by
    intro k hk
    simp [x, not_lt.mpr hk]
  refine ⟨x, fun k => μ k (x k.castSucc), ⟨hx_before t le_rfl, fun i hi => ?_⟩, ?_⟩
  · exact ⟨hμmem i _, hx_after i hi⟩
  · intro i _ a ha
    exact hμmin i _ a ha

/-- The value extended to the vertices of the stage-indexed graph, zero at the sink. -/
private def vertexValue (V : Fin (N + 1) → S → ℝ) : P.StageVertex → ℝ
  | .node t s => V t s
  | .sink => 0

/-- Along every arc, the extended value decreases by at most the arc length. -/
private theorem vertexValue_le_arc (hV_last : ∀ s, V (Fin.last N) s = P.terminalCost s)
    (hV : ∀ (i : Fin N) (s : S), V i.castSucc s =
      (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
        P.cost i s a + V i.succ (P.transition i s a))
    {v w : P.StageVertex} (e : v ⟶ w) :
    vertexValue V v ≤ P.stageArcLength e + vertexValue V w := by
  cases e with
  | step i s a ha =>
    simp only [vertexValue, stageArcLength]
    rw [hV]
    exact inf'_le _ ha
  | exit s => simp [vertexValue, stageArcLength, hV_last]

/-- No path to a vertex is shorter than the drop of the extended value along it. -/
private theorem vertexValue_le_path (hV_last : ∀ s, V (Fin.last N) s = P.terminalCost s)
    (hV : ∀ (i : Fin N) (s : S), V i.castSucc s =
      (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
        P.cost i s a + V i.succ (P.transition i s a))
    {v w : P.StageVertex} (p : Quiver.Path v w) :
    vertexValue V v ≤ p.addWeight P.stageArcLength + vertexValue V w := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Quiver.Path.addWeight_cons]
    have he := vertexValue_le_arc hV_last hV e
    linarith

/-- From every vertex `(t, s)` some path to the sink has length `V t s`. -/
private theorem exists_path (hV_last : ∀ s, V (Fin.last N) s = P.terminalCost s)
    (hV : ∀ (i : Fin N) (s : S), V i.castSucc s =
      (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
        P.cost i s a + V i.succ (P.transition i s a))
    (t : Fin (N + 1)) (s : S) :
    ∃ p : Quiver.Path (V := P.StageVertex) (StageVertex.node t s) StageVertex.sink,
      p.addWeight P.stageArcLength = V t s := by
  induction t using Fin.reverseInduction generalizing s with
  | last =>
    refine ⟨Quiver.Hom.toPath (V := P.StageVertex) (StageArc.exit s), ?_⟩
    simp [Quiver.Hom.toPath, stageArcLength, hV_last]
  | cast i ih =>
    obtain ⟨a, ha, haeq⟩ := exists_mem_eq_inf' (P.admissible_nonempty i s)
      fun a => P.cost i s a + V i.succ (P.transition i s a)
    obtain ⟨q, hq⟩ := ih (P.transition i s a)
    refine ⟨(Quiver.Hom.toPath (V := P.StageVertex) (StageArc.step i s a ha)).comp q, ?_⟩
    rw [Quiver.Path.addWeight_comp, hq, hV, haeq]
    simp [Quiver.Hom.toPath, stageArcLength]

end Recursion

/-- **Backward induction for deterministic finite-horizon control.** Let $V$ satisfy $V_N = g$
and $V_t(s) = \min_{a \in A_t(s)} \bigl(c_t(s, a) + V_{t+1}(F_t(s, a))\bigr)$ for $t < N$. Then,
for every stage $t \le N$ and state $s$:

1. $V_t(s)$ is the minimum of the total cost $\sum_{t \le i < N} c_i(x_i, u_i) + g(x_N)$ over
   the admissible sequences from $s$ at stage $t$: states $x$ and actions $u$ with $x_t = s$,
   $u_i \in A_i(x_i)$ and $x_{i+1} = F_i(x_i, u_i)$ for $t \le i < N$;
2. an admissible sequence from $s$ at stage $t$ whose action $u_i$, at each stage
   $t \le i < N$, minimizes $c_i(x_i, a) + V_{i+1}(F_i(x_i, a))$ over $a \in A_i(x_i)$ has total
   cost $V_t(s)$, so it is optimal;
3. $V_t(s)$ is the minimum length of a path from $(t, s)$ to the sink in the stage-indexed graph,
   whose arcs are an arc $(i, s') \to (i + 1, F_i(s', a))$ of length $c_i(s', a)$ for each
   admissible action $a \in A_i(s')$ and an arc from $(N, s')$ to the sink of length $g(s')$ for
   each state $s'$. -/
theorem backward_induction (V : Fin (N + 1) → S → ℝ)
    (hV_last : ∀ s, V (Fin.last N) s = P.terminalCost s)
    (hV : ∀ (i : Fin N) (s : S), V i.castSucc s =
      (P.admissible i s).inf' (P.admissible_nonempty i s) fun a =>
        P.cost i s a + V i.succ (P.transition i s a))
    (t : Fin (N + 1)) (s : S) :
    IsLeast {J | ∃ x u, P.IsAdmissibleSequence t s x u ∧ P.totalCost t x u = J} (V t s) ∧
    (∀ x u, P.IsAdmissibleSequence t s x u →
      (∀ i : Fin N, t ≤ i.castSucc → ∀ a ∈ P.admissible i (x i.castSucc),
        P.cost i (x i.castSucc) (u i) + V i.succ (P.transition i (x i.castSucc) (u i)) ≤
          P.cost i (x i.castSucc) a + V i.succ (P.transition i (x i.castSucc) a)) →
      P.totalCost t x u = V t s) ∧
    IsLeast (Set.range fun p : Quiver.Path (V := P.StageVertex) (StageVertex.node t s)
      StageVertex.sink => p.addWeight P.stageArcLength) (V t s) := by
  refine ⟨⟨?_, ?_⟩, fun x u h hmin => totalCost_eq_of_minimizing hV_last hV h hmin, ⟨?_, ?_⟩⟩
  · obtain ⟨x, u, h, hmin⟩ := exists_minimizing (P := P) (V := V) t s
    exact ⟨x, u, h, totalCost_eq_of_minimizing hV_last hV h hmin⟩
  · rintro J ⟨x, u, h, rfl⟩
    exact le_totalCost hV_last hV h
  · obtain ⟨p, hp⟩ := exists_path hV_last hV t s
    exact ⟨p, hp⟩
  · rintro J ⟨p, rfl⟩
    simpa [vertexValue] using vertexValue_le_path hV_last hV p

/-- The stage of a vertex, with the sink after stage `N`. -/
private def rank : P.StageVertex → ℕ
  | .node t _ => t
  | .sink => N + 1

private theorem rank_path {v w : P.StageVertex} (p : Quiver.Path v w) :
    P.rank w = P.rank v + p.length := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Quiver.Path.length_cons, ← add_assoc, ← ih]
    cases e with
    | step => simp [rank]
    | exit => simp [rank]

/-- **The stage-indexed graph is acyclic.** In the stage-indexed graph of a deterministic control
problem, every path from a vertex to itself is the trivial path. -/
theorem stageArc_acyclic {v : P.StageVertex} (p : Quiver.Path v v) : p = Quiver.Path.nil :=
  Quiver.Path.eq_nil_of_length_zero p (by have := P.rank_path p; omega)

theorem backwardValue_spec (t : Fin (N + 1)) (s : S) :
    IsLeast {J | ∃ x u, P.IsAdmissibleSequence t s x u ∧ P.totalCost t x u = J}
      (P.backwardValue t s) ∧
    (∀ x u, P.IsAdmissibleSequence t s x u →
      (∀ i : Fin N, t ≤ i.castSucc → ∀ a ∈ P.admissible i (x i.castSucc),
        P.cost i (x i.castSucc) (u i) +
            P.backwardValue i.succ (P.transition i (x i.castSucc) (u i)) ≤
          P.cost i (x i.castSucc) a + P.backwardValue i.succ (P.transition i (x i.castSucc) a)) →
      P.totalCost t x u = P.backwardValue t s) ∧
    IsLeast (Set.range fun p : Quiver.Path (V := P.StageVertex) (StageVertex.node t s)
      StageVertex.sink => p.addWeight P.stageArcLength) (P.backwardValue t s) :=
  P.backward_induction P.backwardValue (by simp) P.backwardValue_castSucc t s

end ControlProblem

end Cslib.Algorithms.Lean.DeterministicFiniteHorizon
