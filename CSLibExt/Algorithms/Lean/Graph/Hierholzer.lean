/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Perm.Basic

/-!
# Euler circuits by Hierholzer's algorithm

CLRS, third edition, Problem 22-3: a strongly connected directed graph has an Euler tour (a cycle
that traverses each edge exactly once) iff every vertex has equal in-degree and out-degree, and such
a tour can be found in `O(E)` time. Here strong connectivity is weakened to: every edge starts at a
vertex reachable from the start vertex `s`. The algorithm here is Hierholzer's (1873) in its
standard recursive form: from `v`, while `v` has an unused outgoing edge `v → w`, remove it and
recurse at `w`; when `v` has none left, emit `v`. The emitted sequence, built by prepending, is the
circuit.

Graphs are `DirectedAdjacency` values read as multigraphs: every adjacency entry is one edge
occurrence (`edgeList`), so repeated entries are parallel edges, each to be traversed once.

* `IsEulerPath graph s t W`: `W` starts at `s`, ends at `t`, and its consecutive pairs
  (`walkEdges W`) are a permutation of `edgeList graph`; `IsEulerCircuit graph s` is the case
  `t = s`.
* `hierholzer_isEulerCircuit`: if every vertex is balanced (`IsBalanced`) and every edge's source
  is reachable from `s`, `hierholzer graph s` is an Euler circuit from `s`.
* `hierholzer_isEulerPath`: the same algorithm finds an Euler path from `s` to `t` when `s` has one
  more outgoing than incoming edge, `t` one more incoming than outgoing, and every other vertex is
  balanced (`IsSemiBalanced`).
* `isBalanced_of_isEulerCircuit`, `isSemiBalanced_of_isEulerPath`: the converses, so for graphs
  whose edges are reachable from `s` an Euler circuit (path) exists iff the graph is balanced
  (semi-balanced): `exists_isEulerCircuit_iff`, `exists_isEulerPath_iff`.
* `hierholzer_trail`: without the reachability hypothesis, the result is still a walk from `s` to
  `t` that uses each edge occurrence at most once.

The proof follows the recursion: a call at `v` on a remaining multigraph in which `v` has one more
outgoing than incoming edge and some `t` one more incoming than outgoing (`v = t` when balanced)
emits a walk from `v` to `t` and leaves a balanced remainder in which the walk's vertices have no
outgoing edges. This is the public contract `visit_spec` of the recursion `visit`, stated on the
remaining edge list with `SemiBalancedEdges` and `BalancedEdges`.

## Cost model

One unit per edge traversal (removing the head of an adjacency list). Reading an adjacency list
and emitting a vertex are free, as with mutable per-vertex lists. A balanced graph whose edges are
all reachable costs exactly `|E|` (`hierholzer_time`). The executable state is a function
updated with `Function.update`; it models the per-vertex lists, but its own lookups are not
constant time, so the bound is in the model, not for this representation. The emitted circuit is
built by prepending, with no list appends.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Hierholzer

open Cslib.Algorithms.Lean TimeM

universe u

variable {V : Type u} [DecidableEq V]

/-- **Edge list of an adjacency function.** Given a directed adjacency graph $G$ and a function
$R$ assigning to each vertex $u$ a list $R(u)$ of vertices, the edge list of $R$ is the list of
pairs $(u, w)$, one for each entry $w$ of $R(u)$, taken over the vertices $u$ in the order of the
vertex enumeration of $G$ and, for each $u$, in the order of $R(u)$. A repeated entry gives a
repeated pair. -/
def edgeListOf (graph : DirectedAdjacency V) (R : V → List V) : List (V × V) :=
  graph.vertices.flatMap fun u => (R u).map (u, ·)

/-- **Edge list of a directed graph.** The edge list of a directed adjacency graph $G$ is the list
of pairs $(u, w)$, one for each entry $w$ of the adjacency list of $u$, taken over the vertices
$u$ in the order of the vertex enumeration of $G$ and, for each $u$, in adjacency-list order. A
repeated adjacency entry gives a repeated pair, so $G$ is read as a multigraph with one edge
occurrence per entry. -/
def edgeList (graph : DirectedAdjacency V) : List (V × V) := edgeListOf graph graph.adjacency

/-- **Steps of a walk.** For a finite sequence of vertices $W = (w_0, w_1, \dots, w_n)$, the
steps of $W$ are the list of consecutive pairs $((w_0, w_1), (w_1, w_2), \dots, (w_{n-1}, w_n))$,
in order. A sequence with at most one vertex has no steps. -/
def walkEdges (W : List V) : List (V × V) := W.zip W.tail

/-- **Balanced directed multigraph.** A finite directed multigraph, read from its adjacency lists
with each entry $w$ in the list of $u$ counted as one occurrence of the edge $u \to w$, is
balanced when every vertex is the source of as many edge occurrences as it is the target of. -/
def IsBalanced (graph : DirectedAdjacency V) : Prop :=
  ∀ x ∈ graph.vertices,
    ((edgeList graph).map Prod.fst).count x = ((edgeList graph).map Prod.snd).count x

instance (graph : DirectedAdjacency V) : Decidable (IsBalanced graph) := by
  unfold IsBalanced; infer_instance

/-- **Semi-balanced directed multigraph.** A finite directed multigraph is semi-balanced for
vertices $s$ and $t$ when, for every vertex $x$, the number of edge occurrences leaving $x$ plus
$[x = t]$ equals the number entering $x$ plus $[x = s]$, where $[P]$ is $1$ if $P$ holds and $0$
otherwise. So for $s \ne t$, one more edge occurrence leaves $s$ than enters it, one more enters
$t$ than leaves it, and every other vertex is balanced; for $s = t$ every vertex is balanced. -/
def IsSemiBalanced (graph : DirectedAdjacency V) (s t : V) : Prop :=
  ∀ x ∈ graph.vertices,
    ((edgeList graph).map Prod.fst).count x + (if x = t then 1 else 0) =
      ((edgeList graph).map Prod.snd).count x + (if x = s then 1 else 0)

instance (graph : DirectedAdjacency V) (s t : V) : Decidable (IsSemiBalanced graph s t) := by
  unfold IsSemiBalanced; infer_instance

/-- **Euler path in a directed multigraph.** In a finite directed multigraph, a list of vertices
$W = (w_0, \dots, w_k)$ is an Euler path from $s$ to $t$ when $w_0 = s$, $w_k = t$, and its list
of steps $(w_0, w_1), \dots, (w_{k-1}, w_k)$ is a permutation of the list of edge occurrences of
the graph, so that each edge occurrence, counted with multiplicity, is traversed exactly once. -/
def IsEulerPath (graph : DirectedAdjacency V) (s t : V) (W : List V) : Prop :=
  W.head? = some s ∧ W.getLast? = some t ∧ (walkEdges W).Perm (edgeList graph)

instance (graph : DirectedAdjacency V) (s t : V) (W : List V) :
    Decidable (IsEulerPath graph s t W) := by
  unfold IsEulerPath; infer_instance

/-- **Euler circuit in a directed multigraph.** In a finite directed multigraph, a list of
vertices $W$ is an Euler circuit from a vertex $s$ when it is an Euler path from $s$ to $s$: it
starts and ends at $s$, and its list of consecutive pairs is a permutation of the list of edge
occurrences of the graph. -/
def IsEulerCircuit (graph : DirectedAdjacency V) (s : V) (W : List V) : Prop :=
  IsEulerPath graph s s W

instance (graph : DirectedAdjacency V) (s : V) (W : List V) :
    Decidable (IsEulerCircuit graph s W) := by
  unfold IsEulerCircuit; infer_instance

/-! ## The algorithm -/

/-- **Hierholzer's recursion.** Given a fuel $n$, a vertex $v$, an assignment $R$ of a list of
remaining out-neighbours to each vertex, and a list $\mathit{acc}$ of vertices, the recursion
returns a list of vertices and a new assignment, with a cost. With fuel $0$ it returns
$(\mathit{acc}, R)$ at cost $0$. With fuel $n + 1$: if $R(v)$ is empty, it returns $v$ followed by
$\mathit{acc}$ together with $R$, at cost $0$; otherwise $R(v)$ is $w$ followed by a list
$\mathit{rest}$, and it replaces $R(v)$ by $\mathit{rest}$, runs the recursion with fuel $n$ from
$w$ on the new assignment with accumulator $\mathit{acc}$, obtaining $(L_1, R_1)$, and returns the
result of the recursion with fuel $n$ from $v$ on $R_1$ with accumulator $L_1$, at cost $1$ plus
the costs of the two calls.

This follows unused edges depth first and splices sub-tours in; too little fuel can stop it
early. Hierholzer's algorithm runs it with fuel one more than the number of edge occurrences. -/
def visit : ℕ → V → (V → List V) → List V → TimeM ℕ (List V × (V → List V))
  | 0, _, R, acc => pure (acc, R)
  | fuel + 1, v, R, acc =>
      match R v with
      | [] => pure (v :: acc, R)
      | w :: rest => do
          ✓
          let r ← visit fuel w (Function.update R v rest) acc
          visit fuel v r.2 r.1

/-- **Hierholzer's algorithm.** Let $G$ be a directed adjacency graph, read as a multigraph with
one edge occurrence per adjacency entry, let $s$ be a vertex, and let $m$ be the number of edge
occurrences of $G$, that is, the length of its edge list. Hierholzer's algorithm on $G$ from $s$
runs Hierholzer's recursion from $s$ with fuel $m + 1$, with the adjacency list of each vertex as
its list of remaining out-neighbours and the empty list as accumulator, and returns the list of
vertices produced by the recursion, at the cost of the recursion. -/
def hierholzer (graph : DirectedAdjacency V) (s : V) : TimeM ℕ (List V) := do
  let r ← visit ((edgeList graph).length + 1) s graph.adjacency []
  pure r.1

/-! ## Edge lists -/

omit [DecidableEq V] in
private theorem mem_edgeListOf {graph : DirectedAdjacency V} {R : V → List V} {a b : V} :
    (a, b) ∈ edgeListOf graph R ↔ b ∈ R a := by
  simp only [edgeListOf, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, -, b', hb', rfl, rfl⟩; exact hb'
  · intro h; exact ⟨a, graph.vertices_complete a, b, h, rfl, rfl⟩

private theorem flatMap_update_perm (R : V → List V) {v w : V} {rest : List V}
    (hv : R v = w :: rest) : ∀ l : List V, l.Nodup → v ∈ l →
    (l.flatMap fun u => (R u).map (u, ·)).Perm
      ((v, w) :: l.flatMap fun u => (Function.update R v rest u).map (u, ·))
  | [], _, h => absurd h List.not_mem_nil
  | u :: l, hnd, h => by
      rw [List.nodup_cons] at hnd
      simp only [List.flatMap_cons]
      by_cases huv : u = v
      · subst huv
        have hl : (l.flatMap fun x => (Function.update R u rest x).map (x, ·)) =
            l.flatMap fun x => (R x).map (x, ·) := by
          refine List.flatMap_congr fun x hx => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hnd.1 hx)]
        rw [hl, hv, Function.update_self]
        simp
      · have hv' : v ∈ l := by
          rcases List.mem_cons.1 h with h | h
          · exact absurd h.symm huv
          · exact h
        rw [Function.update_of_ne huv]
        exact ((flatMap_update_perm R hv l hnd.2 hv').append_left _).trans List.perm_middle

/-- Traversing `v → w` removes exactly that occurrence from the edge list. -/
private theorem edgeListOf_update_perm (graph : DirectedAdjacency V) {R : V → List V} {v w : V}
    {rest : List V} (hv : R v = w :: rest) :
    (edgeListOf graph R).Perm ((v, w) :: edgeListOf graph (Function.update R v rest)) :=
  flatMap_update_perm R hv _ graph.vertices_nodup (graph.vertices_complete v)

omit [DecidableEq V] in
/-- **Steps of a concatenated walk.** Let $A$ and $B$ be nonempty vertex sequences, where $A$
ends at the vertex $a$ and $B$ starts at the vertex $b$. Then the steps of the concatenation
$A B$ are the steps of $A$, followed by the step $(a, b)$, followed by the steps of $B$. -/
theorem walkEdges_append {A B : List V} {a b : V} (ha : A.getLast? = some a)
    (hb : B.head? = some b) : walkEdges (A ++ B) = walkEdges A ++ (a, b) :: walkEdges B := by
  induction A with
  | nil => simp at ha
  | cons x A ih =>
      cases A with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at ha
          subst ha
          cases B with
          | nil => simp at hb
          | cons y B =>
              simp only [List.head?_cons, Option.some.injEq] at hb
              subst hb
              simp [walkEdges]
      | cons y A =>
          rw [List.getLast?_cons_cons] at ha
          have := ih ha
          simp only [walkEdges, List.cons_append, List.tail_cons, List.zip_cons_cons] at this ⊢
          rw [this]

omit [DecidableEq V] in
/-- **Moving a block of a list in front of an element is a permutation.** For an element $e$ and
lists $A$, $B$, $C$ of the same type, the list $e \cdot A \cdot B \cdot C$ is a permutation of
$B \cdot e \cdot A \cdot C$, where $\cdot$ denotes concatenation and $e$ stands for the
one-element list.

This is how a sub-tour $B$ is spliced in front of the edge $e$. -/
theorem perm_splice {α : Type*} (e : α) (A B C : List α) :
    (e :: (A ++ (B ++ C))).Perm (B ++ e :: A ++ C) := by
  rw [List.append_assoc, List.cons_append]
  refine (List.Perm.cons _ ?_).trans List.perm_middle.symm
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_comm.append_right _

/-! ## Degree bookkeeping -/

private theorem ite_eq_comm_nat (a b : V) :
    (if a = b then 1 else 0 : ℕ) = if b = a then 1 else 0 := by
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- **Semi-balanced edge list.** A list $E$ of ordered pairs of vertices is semi-balanced for
vertices $v$ and $t$ when, for every vertex $x$, the number of pairs in $E$ with first component
$x$ plus $[x = t]$ equals the number with second component $x$ plus $[x = v]$, where $[P]$ is $1$
if $P$ holds and $0$ otherwise. So for $v \ne t$, $v$ has one more outgoing than incoming
occurrence, $t$ one more incoming than outgoing, and every other vertex is balanced; for $v = t$
every vertex is balanced. -/
def SemiBalancedEdges (E : List (V × V)) (v t : V) : Prop :=
  ∀ x, (E.map Prod.fst).count x + (if x = t then 1 else 0) =
    (E.map Prod.snd).count x + (if x = v then 1 else 0)

/-- **Balanced edge list.** A list $E$ of ordered pairs of vertices, read as directed edge
occurrences, is balanced when every vertex $x$ occurs as the first component of exactly as many
entries of $E$ as it occurs as the second component, counted with multiplicity. -/
def BalancedEdges (E : List (V × V)) : Prop :=
  ∀ x, (E.map Prod.fst).count x = (E.map Prod.snd).count x

private theorem bal_of_perm_cons {E E₁ : List (V × V)} {v w t : V} (hp : E.Perm ((v, w) :: E₁))
    (h : SemiBalancedEdges E v t) : SemiBalancedEdges E₁ w t := by
  intro x
  have h1 := (hp.map Prod.fst).count_eq x
  have h2 := (hp.map Prod.snd).count_eq x
  have hx := h x
  simp only [List.map_cons, List.count_cons, beq_iff_eq] at h1 h2
  rw [ite_eq_comm_nat v x] at h1
  rw [ite_eq_comm_nat w x] at h2
  omega

private theorem balanced_of_bal_self {E : List (V × V)} {v : V} (h : SemiBalancedEdges E v v) :
    BalancedEdges E :=
  fun x => by have := h x; omega

private theorem bal_of_balanced {E : List (V × V)} (h : BalancedEdges E) (v : V) :
    SemiBalancedEdges E v v :=
  fun x => by rw [h x]

/-! ## The recursion -/

private theorem visit_zero (v : V) (R : V → List V) (acc : List V) :
    visit 0 v R acc = pure (acc, R) := rfl

private theorem visit_nil {fuel : ℕ} {v : V} {R : V → List V} (acc : List V) (hv : R v = []) :
    visit (fuel + 1) v R acc = pure (v :: acc, R) := by
  simp [visit, hv]

private theorem visit_cons {fuel : ℕ} {v w : V} {R : V → List V} {rest : List V} (acc : List V)
    (hv : R v = w :: rest) :
    (visit (fuel + 1) v R acc).ret =
        (visit fuel v (visit fuel w (Function.update R v rest) acc).ret.2
          (visit fuel w (Function.update R v rest) acc).ret.1).ret ∧
      (visit (fuel + 1) v R acc).time = 1 + (visit fuel w (Function.update R v rest) acc).time +
        (visit fuel v (visit fuel w (Function.update R v rest) acc).ret.2
          (visit fuel w (Function.update R v rest) acc).ret.1).time := by
  constructor
  · simp [visit, hv]
  · simp [visit, hv]; omega

/-- **Contract of Hierholzer's recursion.** Let $G$ be a finite directed multigraph, let $R$
assign to each vertex $u$ a list $R(u)$ of remaining out-neighbours, and let $E(R)$ be the list
of remaining edge occurrences, one pair $(u, w)$ for each entry $w$ of $R(u)$. Let $v$ and $t$ be
vertices, $\mathit{acc}$ a list of vertices and $n$ a natural number with $|E(R)| < n$, and
suppose $E(R)$ is semi-balanced for $v$ and $t$: for every vertex $x$, the number of pairs in
$E(R)$ with first component $x$ plus $[x = t]$ equals the number with second component $x$ plus
$[x = v]$, where $[P]$ is $1$ if $P$ holds and $0$ otherwise. Let $(L, R')$ be the result and $c$
the cost of Hierholzer's recursion with fuel $n$ from $v$ on $R$ with accumulator $\mathit{acc}$.
Then there is a list of vertices $W$ such that $L$ is $W$ followed by $\mathit{acc}$; $W$ starts
at $v$ and ends at $t$; $E(R)$ is a permutation of the steps (consecutive pairs) of $W$ followed
by $E(R')$; every vertex is the first component of as many pairs of $E(R')$ as it is the second
component of; $R'(x)$ is empty for every vertex $x$ of $W$; $R'(x)$ is a suffix of $R(x)$ for
every vertex $x$; and $c + |E(R')| = |E(R)|$. -/
theorem visit_spec (graph : DirectedAdjacency V) : ∀ (fuel : ℕ) (v t : V)
    (R : V → List V) (acc : List V), (edgeListOf graph R).length < fuel →
    SemiBalancedEdges (edgeListOf graph R) v t →
    ∃ W, (visit fuel v R acc).ret.1 = W ++ acc ∧ W.head? = some v ∧ W.getLast? = some t ∧
      (edgeListOf graph R).Perm (walkEdges W ++ edgeListOf graph (visit fuel v R acc).ret.2) ∧
      BalancedEdges (edgeListOf graph (visit fuel v R acc).ret.2) ∧
      (∀ x ∈ W, (visit fuel v R acc).ret.2 x = []) ∧
      (∀ x, (visit fuel v R acc).ret.2 x <:+ R x) ∧
      (visit fuel v R acc).time + (edgeListOf graph (visit fuel v R acc).ret.2).length =
        (edgeListOf graph R).length
  | 0, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, v, t, R, acc, hlen, hbal => by
      rcases hv : R v with _ | ⟨w, rest⟩
      · -- `v` is stuck, so `v = t`
        have hout : ((edgeListOf graph R).map Prod.fst).count v = 0 := by
          rw [List.count_eq_zero]
          intro hm
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hm
          have := mem_edgeListOf.1 hab
          rw [hv] at this
          exact List.not_mem_nil this
        have hvt : v = t := by
          have := hbal v
          rw [hout] at this
          by_contra hne
          simp [hne] at this
        subst hvt
        rw [visit_nil acc hv]
        refine ⟨[v], rfl, rfl, rfl, by simp [walkEdges], balanced_of_bal_self hbal, ?_,
          fun x => List.suffix_refl _, by simp⟩
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact hv
      · have hp := edgeListOf_update_perm graph hv
        set R₁ := Function.update R v rest with hR₁
        have hlen₁ : (edgeListOf graph R₁).length < fuel := by
          have := hp.length_eq; simp only [List.length_cons] at this; omega
        obtain ⟨W₁, hW₁, hW₁h, hW₁l, hp₁, hbal₁, hstuck₁, hsuf₁, htime₁⟩ :=
          visit_spec graph fuel w t R₁ acc hlen₁ (bal_of_perm_cons hp hbal)
        set r₁ := (visit fuel w R₁ acc).ret with hr₁
        have hlen₂ : (edgeListOf graph r₁.2).length < fuel := by
          have := hp₁.length_eq; simp only [List.length_append] at this; omega
        obtain ⟨W₂, hW₂, hW₂h, hW₂l, hp₂, hbal₂, hstuck₂, hsuf₂, htime₂⟩ :=
          visit_spec graph fuel v v r₁.2 r₁.1 hlen₂ (bal_of_balanced hbal₁ v)
        obtain ⟨hret, htime⟩ := visit_cons (fuel := fuel) acc hv
        rw [← hR₁, ← hr₁] at hret htime
        refine ⟨W₂ ++ W₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hret, hW₂, hW₁, List.append_assoc]
        · cases W₂ with
          | nil => simp at hW₂h
          | cons y W₂ => simpa using hW₂h
        · rw [List.getLast?_append_of_ne_nil _ (by rintro rfl; simp at hW₁h)]; exact hW₁l
        · rw [hret, walkEdges_append hW₂l hW₁h]
          exact hp.trans (((hp₁.trans (hp₂.append_left _)).cons _).trans (perm_splice _ _ _ _))
        · rw [hret]; exact hbal₂
        · intro x hx
          rw [hret]
          rcases List.mem_append.1 hx with hx | hx
          · exact hstuck₂ x hx
          · have := hsuf₂ x
            rw [hstuck₁ x hx] at this
            exact List.eq_nil_of_suffix_nil this
        · intro x
          rw [hret]
          refine (hsuf₂ x).trans ((hsuf₁ x).trans ?_)
          by_cases hxv : x = v
          · subst hxv; rw [hR₁, Function.update_self, hv]; exact List.suffix_cons _ _
          · rw [hR₁, Function.update_of_ne hxv]
        · rw [htime, hret]
          have := hp.length_eq
          simp only [List.length_cons] at this
          omega

/-! ## Correctness -/

private theorem hierholzer_facts (graph : DirectedAdjacency V) (s t : V)
    (hbal : IsSemiBalanced graph s t) :
    ∃ R' : V → List V, (hierholzer graph s).ret.head? = some s ∧
      (hierholzer graph s).ret.getLast? = some t ∧
      (edgeList graph).Perm (walkEdges (hierholzer graph s).ret ++ edgeListOf graph R') ∧
      (∀ x ∈ (hierholzer graph s).ret, R' x = []) ∧ (∀ x, R' x <:+ graph.adjacency x) ∧
      (hierholzer graph s).time + (edgeListOf graph R').length = (edgeList graph).length := by
  obtain ⟨W, hW, hh, hl, hp, -, hstuck, hsuf, htime⟩ :=
    visit_spec graph ((edgeList graph).length + 1) s t graph.adjacency [] (Nat.lt_succ_self _)
      (fun x => hbal x (graph.vertices_complete x))
  rw [List.append_nil] at hW
  have hret : (hierholzer graph s).ret = W := by simp [hierholzer, hW]
  have htime' : (hierholzer graph s).time =
      (visit ((edgeList graph).length + 1) s graph.adjacency []).time := by simp [hierholzer]
  refine ⟨_, by rw [hret]; exact hh, by rw [hret]; exact hl, by rw [hret]; exact hp,
    by rw [hret]; exact hstuck, hsuf, by rw [htime']; exact htime⟩

private theorem isSemiBalanced_of_isBalanced {graph : DirectedAdjacency V} (s : V)
    (h : IsBalanced graph) : IsSemiBalanced graph s s :=
  fun x hx => by rw [h x hx]

/-- **Hierholzer's algorithm returns a trail in a directed multigraph.** Let $G$ be a directed
adjacency graph, read as a multigraph with one edge per adjacency entry, and let $s$ and $t$ be
vertices such that $G$ is semi-balanced for $s$ and $t$. Then the vertex sequence $W$ returned by
Hierholzer's algorithm on $G$ from $s$ starts at $s$ and ends at $t$, and the edge list of $G$ is a
permutation of the list of consecutive pairs of $W$ followed by some further list of pairs. So $W$
is a walk from $s$ to $t$ that uses each edge occurrence at most once; reachability is not
assumed. -/
theorem hierholzer_trail (graph : DirectedAdjacency V) (s t : V)
    (hbal : IsSemiBalanced graph s t) :
    (hierholzer graph s).ret.head? = some s ∧ (hierholzer graph s).ret.getLast? = some t ∧
      ∃ rest, (edgeList graph).Perm (walkEdges (hierholzer graph s).ret ++ rest) := by
  obtain ⟨R', hh, hl, hp, -⟩ := hierholzer_facts graph s t hbal
  exact ⟨hh, hl, _, hp⟩

omit [DecidableEq V] in
/-- When every edge's source is reachable from `s`, no edge is left over. -/
private theorem leftover_nil (graph : DirectedAdjacency V) (s : V) {W : List V} {R' : V → List V}
    (hh : W.head? = some s) (hp : (edgeList graph).Perm (walkEdges W ++ edgeListOf graph R'))
    (hstuck : ∀ x ∈ W, R' x = []) (hsuf : ∀ x, R' x <:+ graph.adjacency x)
    (hreach : ∀ u w, graph.Edge u w → graph.Reachable s u) : edgeListOf graph R' = [] := by
  have hmemW : ∀ x, graph.Reachable s x → x ∈ W := by
    intro x hx
    induction hx with
    | refl => exact List.mem_of_mem_head? hh
    | @tail b c _ hbc ih =>
        have hbc' : (b, c) ∈ edgeList graph :=
          mem_edgeListOf.2 (show c ∈ graph.adjacency b from hbc)
        rcases List.mem_append.1 (hp.subset hbc') with h | h
        · exact List.mem_of_mem_tail (List.of_mem_zip h).2
        · have := mem_edgeListOf.1 h
          rw [hstuck b ih] at this
          exact absurd this List.not_mem_nil
  rw [List.eq_nil_iff_forall_not_mem]
  rintro ⟨a, b⟩ hab
  have hb := mem_edgeListOf.1 hab
  have ha := hmemW a (hreach a b ((hsuf a).subset hb))
  rw [hstuck a ha] at hb
  exact List.not_mem_nil hb

/-- **Hierholzer's algorithm finds Euler paths in directed multigraphs.** Let $G$ be a directed
adjacency graph, read as a multigraph with one edge per adjacency entry, and let $s$ and $t$ be
vertices such that $G$ is semi-balanced for $s$ and $t$ (at $s$ one more edge occurrence leaves
than enters, at $t$ one more enters than leaves, and at every other vertex as many leave as enter;
at every vertex when $s = t$) and the source of every edge of $G$ is reachable from $s$. Then the
vertex sequence returned by Hierholzer's algorithm on $G$ from $s$ is an Euler path of $G$ from $s$
to $t$. -/
theorem hierholzer_isEulerPath (graph : DirectedAdjacency V) (s t : V)
    (hbal : IsSemiBalanced graph s t) (hreach : ∀ u w, graph.Edge u w → graph.Reachable s u) :
    IsEulerPath graph s t (hierholzer graph s).ret := by
  obtain ⟨R', hh, hl, hp, hstuck, hsuf, -⟩ := hierholzer_facts graph s t hbal
  have hnil := leftover_nil graph s hh hp hstuck hsuf hreach
  rw [hnil, List.append_nil] at hp
  exact ⟨hh, hl, hp.symm⟩

/-- **Hierholzer's algorithm finds Euler circuits in directed multigraphs.** Let $G$ be a directed
adjacency graph, read as a multigraph with one edge per adjacency entry, that is balanced (every
vertex is the source of exactly as many edge occurrences as it is the target of), and let $s$ be a
vertex such that the source of every edge of $G$ is reachable from $s$. Then the vertex sequence
returned by Hierholzer's algorithm on $G$ from $s$ is an Euler circuit of $G$ from $s$.

Source: CLRS, third edition, Problem 22-3, sufficiency with the algorithm; strong connectivity is
weakened to reachability from $s$ of the source of every edge. -/
theorem hierholzer_isEulerCircuit (graph : DirectedAdjacency V) (s : V)
    (hbal : IsBalanced graph) (hreach : ∀ u w, graph.Edge u w → graph.Reachable s u) :
    IsEulerCircuit graph s (hierholzer graph s).ret :=
  hierholzer_isEulerPath graph s s (isSemiBalanced_of_isBalanced s hbal) hreach

/-- **Running time of Hierholzer's algorithm.** Let $G$ be a directed adjacency graph, read as a
multigraph with one edge per adjacency entry, and let $s$ and $t$ be vertices such that $G$ is
semi-balanced for $s$ and $t$ and the source of every edge of $G$ is reachable from $s$. Then
Hierholzer's algorithm on $G$ from $s$ costs exactly $|E|$ units, where $|E|$ is the number of
edge occurrences of $G$, that is, the length of its edge list.

The cost model charges one unit per edge traversal (removing the head of an adjacency list);
reading an adjacency list and emitting a vertex are free. -/
theorem hierholzer_time (graph : DirectedAdjacency V) (s t : V)
    (hbal : IsSemiBalanced graph s t) (hreach : ∀ u w, graph.Edge u w → graph.Reachable s u) :
    (hierholzer graph s).time = (edgeList graph).length := by
  obtain ⟨R', hh, -, hp, hstuck, hsuf, htime⟩ := hierholzer_facts graph s t hbal
  rw [leftover_nil graph s hh hp hstuck hsuf hreach] at htime
  simpa using htime

/-! ## Necessity -/

private theorem walkEdges_count : ∀ (W : List V) (v t : V), W.head? = some v →
    W.getLast? = some t → ∀ x,
    ((walkEdges W).map Prod.fst).count x + (if x = t then 1 else 0) =
      ((walkEdges W).map Prod.snd).count x + (if x = v then 1 else 0)
  | [], _, _, h, _, _ => by simp at h
  | [a], v, t, hh, hl, x => by
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hh hl
      simp [walkEdges]
  | a :: b :: W, v, t, hh, hl, x => by
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rw [List.getLast?_cons_cons] at hl
      have ih := walkEdges_count (b :: W) b t rfl hl x
      have e : walkEdges (a :: b :: W) = (a, b) :: walkEdges (b :: W) := rfl
      rw [e]
      simp only [List.map_cons, List.count_cons, beq_iff_eq]
      rw [ite_eq_comm_nat a x, ite_eq_comm_nat b x]
      omega

/-- **A directed multigraph with an Euler path is semi-balanced.** If a finite directed
multigraph has an Euler path from $s$ to $t$, then it is semi-balanced for $s$ and $t$: counting
edge occurrences, $s$ has one more outgoing than incoming edge, $t$ one more incoming than
outgoing, and every other vertex is balanced (every vertex, when $s = t$). -/
theorem isSemiBalanced_of_isEulerPath {graph : DirectedAdjacency V} {s t : V} {W : List V}
    (h : IsEulerPath graph s t W) : IsSemiBalanced graph s t := by
  obtain ⟨hh, hl, hp⟩ := h
  intro x _
  have hc := walkEdges_count W s t hh hl x
  rw [← (hp.map Prod.fst).count_eq, ← (hp.map Prod.snd).count_eq]
  exact hc

/-- **A directed multigraph with an Euler circuit is balanced.** If a finite directed multigraph
has an Euler circuit from some vertex $s$, then it is balanced: every vertex is the source of as
many edge occurrences as it is the target of.

This is the necessity direction of CLRS Problem 22-3. -/
theorem isBalanced_of_isEulerCircuit {graph : DirectedAdjacency V} {s : V} {W : List V}
    (h : IsEulerCircuit graph s W) : IsBalanced graph := fun x hx => by
  have := isSemiBalanced_of_isEulerPath h x hx
  omega

/-- **Euler path criterion for directed multigraphs.** Let $G$ be a directed adjacency graph, read
as a multigraph with one edge per adjacency entry, and let $s$ and $t$ be vertices such that the
source of every edge of $G$ is reachable from $s$. Then $G$ has an Euler path from $s$ to $t$ if
and only if $G$ is semi-balanced for $s$ and $t$: at $s$ one more edge occurrence leaves than
enters, at $t$ one more enters than leaves, and every other vertex is the source of exactly as
many edge occurrences as it is the target of (every vertex, when $s = t$). -/
theorem exists_isEulerPath_iff (graph : DirectedAdjacency V) (s t : V)
    (hreach : ∀ u w, graph.Edge u w → graph.Reachable s u) :
    (∃ W, IsEulerPath graph s t W) ↔ IsSemiBalanced graph s t :=
  ⟨fun ⟨_, h⟩ => isSemiBalanced_of_isEulerPath h,
    fun hbal => ⟨_, hierholzer_isEulerPath graph s t hbal hreach⟩⟩

/-- **Euler circuit criterion for directed multigraphs.** Let $G$ be a directed adjacency graph,
read as a multigraph with one edge per adjacency entry, and let $s$ be a vertex such that the
source of every edge of $G$ is reachable from $s$. Then $G$ has an Euler circuit from $s$ if and
only if $G$ is balanced, that is, every vertex is the source of exactly as many edge occurrences
as it is the target of.

Source: CLRS, third edition, Problem 22-3; strong connectivity is weakened to reachability from
$s$ of the source of every edge. -/
theorem exists_isEulerCircuit_iff (graph : DirectedAdjacency V) (s : V)
    (hreach : ∀ u w, graph.Edge u w → graph.Reachable s u) :
    (∃ W, IsEulerCircuit graph s W) ↔ IsBalanced graph :=
  ⟨fun ⟨_, h⟩ => isBalanced_of_isEulerCircuit h,
    fun hbal => ⟨_, hierholzer_isEulerCircuit graph s hbal hreach⟩⟩

end Cslib.Algorithms.Lean.Hierholzer
