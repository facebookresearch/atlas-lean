/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Hamiltonian-cycle to traveling-salesperson reduction

CLRS, fourth edition, Section 34.5.4, Theorem 34.14, printed pages 1090–1092.
The actual one-pass converter negates every supplied adjacency bit, with one read and one
write event per cell. On an encoded simple graph this gives source 0/1 costs, diagonal one,
and threshold zero. Tours are canonical strict Hamiltonian walks; optional accesses include
every dart, including the closing edge. Arbitrary malformed arrays remain total inputs.

This development proves the reduction and the selected same-run event count, not the full
NP-completeness argument or physical RAM, word/bit, allocation, array-growth or space costs.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Graph

/-- **Hamiltonian-cycle to TSP converter.** The Hamiltonian-cycle to TSP converter takes a Boolean
array $x$ and, starting from the empty array, scans $x$ from left to right and appends the
negation of each cell, charging one time unit before and one time unit after each append (one
read and one write per cell). It returns the resulting array of negated cells together with the
total time charged. -/
def hamiltonianCycleToTsp (x : Array Bool) : TimeM Nat (Array Bool) :=
  x.foldlM (fun out bit => do
    TimeM.tick (1 : Nat)
    let out := out.push (!bit)
    TimeM.tick (1 : Nat)
    pure out) #[]

private lemma fold_ret (xs : List Bool) (out : Array Bool) :
    (xs.foldlM (fun out bit => do
      TimeM.tick (1 : Nat)
      let out := out.push (!bit)
      TimeM.tick (1 : Nat)
      pure out) out : TimeM Nat (Array Bool)).ret.toList =
        out.toList ++ xs.map Bool.not := by
  induction xs generalizing out with
  | nil => simp
  | cons bit xs ih =>
    simp only [List.foldlM_cons, TimeM.ret_bind]
    change (xs.foldlM (m := TimeM Nat) _ (out.push (!bit))).ret.toList =
      out.toList ++ ((!bit) :: xs.map Bool.not)
    rw [ih, Array.toList_push, List.append_assoc]
    rfl

private lemma fold_time (xs : List Bool) (out : Array Bool) :
    (xs.foldlM (fun out bit => do
      TimeM.tick (1 : Nat)
      let out := out.push (!bit)
      TimeM.tick (1 : Nat)
      pure out) out : TimeM Nat (Array Bool)).time = 2 * xs.length := by
  induction xs generalizing out with
  | nil => simp
  | cons bit xs ih =>
    simp only [List.foldlM_cons, TimeM.time_bind]
    change 2 + (xs.foldlM (m := TimeM Nat) _ (out.push (!bit))).time =
      2 * (xs.length + 1)
    rw [ih]
    omega

private lemma ret_toList (x : Array Bool) :
    (hamiltonianCycleToTsp x).ret.toList = x.toList.map Bool.not := by
  unfold hamiltonianCycleToTsp
  rw [← Array.foldlM_toList]
  simpa using fold_ret x.toList #[]

/-- **The Hamiltonian-cycle to TSP converter preserves length.** For every Boolean array $x$, the
array output by the Hamiltonian-cycle to TSP converter on $x$ has the same length as $x$.

No assumption that $x$ encodes a graph is needed. -/
theorem hamiltonianCycleToTsp_size (x : Array Bool) :
    (hamiltonianCycleToTsp x).ret.size = x.size := by
  have h := congrArg List.length (ret_toList x)
  simpa using h

/-- **The Hamiltonian-cycle to TSP converter negates every cell.** For every Boolean array $x$ and
every index $k$, the array output by the Hamiltonian-cycle to TSP converter on $x$ has a cell at
index $k$ exactly when $x$ does, and that cell is the negation of the cell of $x$ at index $k$. -/
theorem hamiltonianCycleToTsp_getElem? (x : Array Bool) (k : Nat) :
    (hamiltonianCycleToTsp x).ret[k]? = x[k]?.map Bool.not := by
  rw [← Array.getElem?_toList, ret_toList, List.getElem?_map, Array.getElem?_toList]

/-- **Running time of the Hamiltonian-cycle to TSP converter.** For every Boolean array $x$, the
time charged by the Hamiltonian-cycle to TSP converter on $x$ is $2m$, where $m$ is the length of
$x$: one unit for reading and one unit for writing each cell. -/
theorem hamiltonianCycleToTsp_time (x : Array Bool) :
    (hamiltonianCycleToTsp x).time = 2 * x.size := by
  unfold hamiltonianCycleToTsp
  rw [← Array.foldlM_toList]
  simpa using fold_time x.toList #[]

/-- **Costs produced by the Hamiltonian-cycle to TSP converter.** Let $G$ be a simple graph on the
vertex set $\{0, \dots, n-1\}$, let $x$ be a Boolean array of length $n^2$ such that for all
$i, j < n$ the cell of $x$ at index $in + j$ exists and is true exactly when $i$ and $j$ are
adjacent in $G$, and let $y$ be the array output by the Hamiltonian-cycle to TSP converter on $x$,
with a Boolean cell read as $1$ if true and $0$ if false. Then for all $i, j < n$ the cell of $y$
at index $in + j$ exists and equals $0$ if $i$ and $j$ are adjacent in $G$ and $1$ otherwise; for
every $i < n$ the cell of $y$ at index $in + i$ exists and equals $1$; and for all $i, j < n$ the
cells of $y$ at indices $in + j$ and $jn + i$ are equal. -/
theorem hamiltonianCycleToTsp_costs (x : Array Bool) (n : Nat)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (_hsize : x.size = n * n)
    (henc : ∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j))) :
    (∀ i j : Fin n,
      ((hamiltonianCycleToTsp x).ret[i.val * n + j.val]?).map Bool.toNat =
        some (if G.Adj i j then 0 else 1)) ∧
    (∀ i : Fin n,
      ((hamiltonianCycleToTsp x).ret[i.val * n + i.val]?).map Bool.toNat = some 1) ∧
    (∀ i j : Fin n,
      (hamiltonianCycleToTsp x).ret[i.val * n + j.val]? =
        (hamiltonianCycleToTsp x).ret[j.val * n + i.val]?) := by
  have hcost (i j : Fin n) :
      ((hamiltonianCycleToTsp x).ret[i.val * n + j.val]?).map Bool.toNat =
        some (if G.Adj i j then 0 else 1) := by
    rw [hamiltonianCycleToTsp_getElem?, henc]
    by_cases h : G.Adj i j <;> simp [h]
  refine ⟨hcost, ?_, ?_⟩
  · intro i
    simpa using hcost i i
  · intro i j
    rw [hamiltonianCycleToTsp_getElem?, hamiltonianCycleToTsp_getElem?, henc, henc]
    simp only [G.adj_comm]

private lemma mapped_walk_zero (x : Array Bool) (n : Nat)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hsize : x.size = n * n)
    (henc : ∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j)))
    {a b : Fin n} (p : G.Walk a b) :
    (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).darts.mapM
        (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
          Bool.toNat) = some (List.replicate p.length 0) := by
  have hzero (i j : Fin n) (h : G.Adj i j) :
      ((hamiltonianCycleToTsp x).ret[i.val * n + j.val]?).map Bool.toNat = some 0 := by
    simpa [h] using (hamiltonianCycleToTsp_costs x n G hsize henc).1 i j
  induction p with
  | nil => simp [SimpleGraph.Walk.mapLe]
  | @cons u v w h p ih =>
    simp only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.map_cons,
      SimpleGraph.Walk.darts_cons, List.mapM_cons]
    change (do
      let head ← ((hamiltonianCycleToTsp x).ret[u.val * n + v.val]?).map Bool.toNat
      let tail ← (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).darts.mapM
        (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
          Bool.toNat)
      pure (head :: tail)) = some (List.replicate (p.length + 1) 0)
    rw [hzero u v h, ih]
    simp [List.replicate_succ]

/-- **Hamiltonian cycles of the source graph give zero-cost tours.** Let $G$ be a simple graph on
the vertex set $\{0, \dots, n-1\}$, let $x$ be a Boolean array of length $n^2$ such that for all
$i, j < n$ the cell of $x$ at index $in + j$ exists and is true exactly when $i$ and $j$ are
adjacent in $G$, and let $y$ be the array output by the Hamiltonian-cycle to TSP converter on $x$,
with a Boolean cell read as $1$ if true and $0$ if false. Let $p$ be a Hamiltonian cycle in $G$
based at a vertex $a$, and let $p'$ be $p$ regarded as a closed walk in the complete graph on
$\{0, \dots, n-1\}$. Then $p'$ is a Hamiltonian cycle, $p'$ visits the same sequence of vertices
as $p$, and for every directed edge $(u, v)$ traversed by $p'$ the cell of $y$ at index $un + v$
exists, and the sum of these cells over the directed edges of $p'$ is $0$. -/
theorem hamiltonianCycleToTsp_forward (x : Array Bool) (n : Nat)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hsize : x.size = n * n)
    (henc : ∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j)))
    (a : Fin n) (p : G.Walk a a) (hp : p.IsHamiltonianCycle) :
    (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).IsHamiltonianCycle ∧
    (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).support = p.support ∧
    ∃ costs : List Nat,
      (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).darts.mapM
          (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
            Bool.toNat) = some costs ∧ costs.sum = 0 := by
  refine ⟨hp.map Function.bijective_id,
    SimpleGraph.Walk.support_mapLe_eq_support _ _, List.replicate p.length 0,
    mapped_walk_zero x n G hsize henc p, ?_⟩
  simp

private lemma edges_of_cost_zero (x : Array Bool) (n : Nat)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hsize : x.size = n * n)
    (henc : ∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j)))
    {a b : Fin n} (p : (SimpleGraph.completeGraph (Fin n)).Walk a b)
    (costs : List Nat)
    (hmap : p.darts.mapM
      (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
        Bool.toNat) = some costs)
    (hsum : costs.sum ≤ 0) : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
  have hcost := (hamiltonianCycleToTsp_costs x n G hsize henc).1
  induction p generalizing costs with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.mapM_cons] at hmap
    change (do
      let head ← ((hamiltonianCycleToTsp x).ret[u.val * n + v.val]?).map Bool.toNat
      let tail ← p.darts.mapM
        (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
          Bool.toNat)
      pure (head :: tail)) = some costs at hmap
    rw [hcost u v] at hmap
    cases ht : p.darts.mapM
        (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
          Bool.toNat) with
    | none => simp [ht] at hmap
    | some tail =>
      have heq : (if G.Adj u v then 0 else 1) :: tail = costs := by
        simpa [ht] using hmap
      rw [← heq, List.sum_cons] at hsum
      have hadj : G.Adj u v := by
        by_contra hnot
        simp [hnot] at hsum
      have htail : tail.sum ≤ 0 := by
        simpa [hadj] using hsum
      intro e he
      rw [SimpleGraph.Walk.edges_cons] at he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact hadj
      · exact ih tail ht htail e he

/-- **Tours of cost zero give Hamiltonian cycles of the source graph.** Let $G$ be a simple graph
on the vertex set $\{0, \dots, n-1\}$, let $x$ be a Boolean array of length $n^2$ such that for
all $i, j < n$ the cell of $x$ at index $in + j$ exists and is true exactly when $i$ and $j$ are
adjacent in $G$, and let $y$ be the array output by the Hamiltonian-cycle to TSP converter on $x$,
with a Boolean cell read as $1$ if true and $0$ if false. Let $p$ be a Hamiltonian cycle based at
a vertex $a$ in the complete graph on $\{0, \dots, n-1\}$ such that for every directed edge
$(u, v)$ traversed by $p$ the cell of $y$ at index $un + v$ exists and the sum of these cells over
the directed edges of $p$ is at most $0$. Then there is a Hamiltonian cycle $q$ in $G$ based at
$a$ that visits the same sequence of vertices as $p$. -/
theorem hamiltonianCycleToTsp_reverse (x : Array Bool) (n : Nat)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hsize : x.size = n * n)
    (henc : ∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j)))
    (a : Fin n) (p : (SimpleGraph.completeGraph (Fin n)).Walk a a)
    (hp : p.IsHamiltonianCycle)
    (hcost : ∃ costs : List Nat,
      p.darts.mapM
        (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
          Bool.toNat) = some costs ∧ costs.sum ≤ 0) :
    ∃ q : G.Walk a a, q.IsHamiltonianCycle ∧ q.support = p.support := by
  obtain ⟨costs, hmap, hsum⟩ := hcost
  have hedge := edges_of_cost_zero x n G hsize henc p costs hmap hsum
  exact ⟨p.transfer G hedge, hp.transfer hedge, SimpleGraph.Walk.support_transfer p hedge⟩

/-- **Correctness of the Hamiltonian-cycle to TSP reduction.** Let $G$ be a simple graph on the
vertex set $V = \{0, \dots, n-1\}$, let $x$ be a Boolean array of length $n^2$ such that for all
$i, j < n$ the cell of $x$ at index $in + j$ exists and is true exactly when $i$ and $j$ are
adjacent in $G$, and let $y$ be the array output by the Hamiltonian-cycle to TSP converter on $x$,
with a Boolean cell read as $1$ if true and $0$ if false. Then $G$ has a Hamiltonian cycle if and
only if the complete graph on $V$ has a Hamiltonian cycle $p$ such that for every directed edge
$(u, v)$ traversed by $p$ the cell of $y$ at index $un + v$ exists and the sum of these cells over
the directed edges of $p$ is at most $0$. -/
theorem hamiltonianCycleToTsp_iff (x : Array Bool) (n : Nat)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hsize : x.size = n * n)
    (henc : ∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j))) :
    ((∃ (a : Fin n) (p : G.Walk a a), p.IsHamiltonianCycle) ↔
      ∃ (a : Fin n) (p : (SimpleGraph.completeGraph (Fin n)).Walk a a),
        p.IsHamiltonianCycle ∧ ∃ costs : List Nat,
          p.darts.mapM
            (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map
              Bool.toNat) = some costs ∧ costs.sum ≤ 0) := by
  constructor
  · rintro ⟨a, p, hp⟩
    obtain ⟨hcycle, _, costs, hmap, hsum⟩ :=
      hamiltonianCycleToTsp_forward x n G hsize henc a p hp
    exact ⟨a, p.mapLe le_top, hcycle, costs, hmap, hsum.le⟩
  · rintro ⟨a, p, hp, hcost⟩
    obtain ⟨q, hq, _⟩ := hamiltonianCycleToTsp_reverse x n G hsize henc a p hp hcost
    exact ⟨a, q, hq⟩

end Cslib.Algorithms.Lean.Graph
