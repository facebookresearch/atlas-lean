/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Infix
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Karger's contraction algorithm for minimum cuts

Karger's algorithm (D. R. Karger, *Global min-cuts in RNC, and other ramifications of a simple
min-cut algorithm*, SODA 1993; Kleinberg and Tardos, *Algorithm Design*, Section 13.2; Motwani
and Raghavan, *Randomized Algorithms*, Section 1.1): while the multigraph has more than two
(super-)vertices, contract a uniformly random edge, merging its endpoints and deleting the
self-loops this creates; return the number of edges between the last two vertices.

Theorem (`successProb_ge`): if the multigraph on `n ≥ 2` vertices has minimum cut size `k`, one
run returns `k` with probability at least `2 / (n (n - 1))`. Amplification
(`repeatSuccessProb_ge_half`): `n (n - 1) / 2` independent runs find `k` with probability at least
`1 / 2`, `c · n (n - 1) / 2` runs with probability at least `1 - (1/2)^c` (`repeatSuccessProb_ge`),
and `⌈log₂ n⌉ · n (n - 1) / 2` runs with probability at least `1 - 1/n`
(`repeatSuccessProb_ge_one_sub_inv`).

The proof follows the textbook. A minimum cut `X` survives a contraction unless the chosen edge
crosses it; contraction never creates smaller cuts (every cut of the contracted multigraph is a
cut of the original of the same size, `cutSize_contract`), so `X` stays a minimum cut. Every
vertex has degree at least `k` (its singleton is a cut), so there are at least `n k / 2` edges and
the chosen edge crosses `X` with probability at most `2 / n`. Multiplying
`(1 - 2/n) (1 - 2/(n-1)) ⋯ (1 - 2/3)` gives `2 / (n (n - 1))`.

## Model

A `State` is a list of current super-vertices and a list of edges between them (a multigraph:
repeated pairs are parallel edges). `contract st e` merges `e.2` into `e.1`. The randomness is
modelled exactly by `successProb k`: the probability that the process ends with `k` crossing
edges, computed by the law of total probability over the uniformly chosen edge. It is an exact
rational, so small cases can be evaluated (`KargerMinCutTests`).

## Counting minimum cuts

Corollary (`two_mul_length_minCuts_le`; Kleinberg and Tardos, Section 13.2): a connected
multigraph on `n ≥ 2` vertices (minimum cut size `k ≥ 1`) has at most `n (n - 1) / 2` minimum
cuts, counted as partitions (`DistinctOn`: two cuts that differ somewhere and agree somewhere).
`surviveProb X` is the probability that a run never contracts an edge crossing `X` and ends with
two vertices that `X` separates, i.e. that the run outputs `X`. Each minimum cut survives with
probability at least `2 / (n (n - 1))` (`surviveProb_ge`, the argument above for a fixed cut), and
a run outputs at most one partition, so the survival probabilities of pairwise distinct cuts add
up to at most `1` (`sum_surviveProb_le_one`). The `n`-cycle attains the bound.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Karger

universe u

variable {V : Type u} [DecidableEq V]

/-- **Multigraph state of Karger's algorithm.** A state over a vertex type $V$ consists of a
list of current (super-)vertices in $V$ and a list of edges, each an ordered pair of elements
of $V$; repeated pairs are parallel edges. -/
structure State (V : Type u) where
  /-- The current vertices. -/
  verts : List V
  /-- The edges, with multiplicity. -/
  edges : List (V × V)

/-- **Valid multigraph.** A multigraph, given by a list of vertices and a list of edges (pairs of
vertices, with multiplicity), is valid when its vertex list has no repeated entries and every
edge joins two distinct vertices of the list. -/
def State.Valid (st : State V) : Prop :=
  st.verts.Nodup ∧ ∀ e ∈ st.edges, e.1 ∈ st.verts ∧ e.2 ∈ st.verts ∧ e.1 ≠ e.2

/-- **Size of a cut.** For a list of edges (pairs of vertices, repeated pairs counted with
multiplicity) and a map $X$ from vertices to booleans, the size of the cut $X$ is the number of
edges $(u, v)$ in the list with $X(u) \ne X(v)$. -/
def cutSize (edges : List (V × V)) (X : V → Bool) : ℕ :=
  (edges.filter fun e => X e.1 != X e.2).length

/-- **Cuts of a multigraph.** A map $X$ from vertices to booleans is a cut of a multigraph state
$G$ when some vertex $v$ of $G$ has $X(v) = \mathrm{true}$ and some vertex $w$ of $G$ has
$X(w) = \mathrm{false}$. -/
def IsCut (st : State V) (X : V → Bool) : Prop :=
  (∃ v ∈ st.verts, X v = true) ∧ ∃ v ∈ st.verts, X v = false

/-- **Minimum cut size.** A natural number $k$ is the minimum cut size of a multigraph state $G$
when some cut of $G$ has size $k$ and every cut of $G$ has size at least $k$. -/
def IsMinCut (st : State V) (k : ℕ) : Prop :=
  (∃ X, IsCut st X ∧ cutSize st.edges X = k) ∧ ∀ X, IsCut st X → k ≤ cutSize st.edges X

/-- **Renaming a vertex.** For vertices $a$ and $b$, renaming $b$ to $a$ is the map on vertices
that sends $b$ to $a$ and fixes every other vertex. -/
def rename (b a v : V) : V := if v = b then a else v

/-- **Edge contraction.** For a multigraph state $G$ and a pair of vertices $e = (a, b)$, the
contraction of $G$ along $e$ deletes the first occurrence of $b$ from the vertex list, replaces
$b$ by $a$ in both endpoints of every edge, and then deletes every edge whose two endpoints are
equal. -/
def contract (st : State V) (e : V × V) : State V where
  verts := st.verts.erase e.2
  edges := (st.edges.map fun x => (rename e.2 e.1 x.1, rename e.2 e.1 x.2)).filter
    fun x => x.1 ≠ x.2

/-- **Success probability of the contraction process.** For a natural number $k$, a number $f$
of allowed contractions and a multigraph $G$ with edge list $E_G$, the probability $P_k(f, G)$
that the contraction process on $G$ returns $k$ is defined by recursion on $f$. If $f = 0$, or
$G$ has at most two vertices, or $G$ has no edges, then $P_k(f, G)$ is $1$ when $G$ has exactly
$k$ edges and $0$ otherwise. Otherwise
$P_k(f, G) = \frac{1}{|E_G|} \sum_{e \in E_G} P_k(f - 1, G/e)$, where $G/e$ is the contraction of
$G$ along $e$ and the sum runs over the edges with multiplicity.

This models contracting a uniformly random edge while more than two vertices remain and counting
the edges between the last two vertices. -/
def successProb (k : ℕ) : ℕ → State V → ℚ
  | 0, st => if st.edges.length = k then 1 else 0
  | fuel + 1, st =>
      if st.verts.length ≤ 2 ∨ st.edges = [] then (if st.edges.length = k then 1 else 0)
      else (st.edges.map fun e => successProb k fuel (contract st e)).sum / st.edges.length

/-! ## Contraction and cuts -/

/-- **Cut sizes under contraction.** Let $G$ be a multigraph state, $e = (a, b)$ a pair of
vertices and $Y$ a map from vertices to booleans, and let $\rho$ send $b$ to $a$ and fix every
other vertex. The size of the cut $Y$ in the contraction of $G$ along $e$ equals the size of the
cut $Y \circ \rho$ in $G$. -/
theorem cutSize_contract (st : State V) (e : V × V) (Y : V → Bool) :
    cutSize (contract st e).edges Y = cutSize st.edges fun v => Y (rename e.2 e.1 v) := by
  simp only [cutSize, contract, List.filter_filter]
  have h : ∀ x ∈ st.edges.map (fun x => (rename e.2 e.1 x.1, rename e.2 e.1 x.2)),
      ((Y x.1 != Y x.2) && decide (x.1 ≠ x.2)) = (Y x.1 != Y x.2) := by
    intro x _
    by_cases hx : x.1 = x.2
    · simp [hx]
    · simp [hx]
  rw [List.filter_congr h, List.filter_map, List.length_map]
  rfl

omit [DecidableEq V] in
private theorem mem_erase_of_nodup {l : List V} (hnd : l.Nodup) {b v : V} [DecidableEq V] :
    v ∈ l.erase b ↔ v ≠ b ∧ v ∈ l := hnd.mem_erase_iff

/-- A cut of the contraction lifts to a cut of the original. -/
private theorem isCut_lift {st : State V} (hv : st.Valid) {e : V × V} {Y : V → Bool}
    (hY : IsCut (contract st e) Y) : IsCut st fun v => Y (rename e.2 e.1 v) := by
  obtain ⟨⟨v, hv1, hv2⟩, ⟨w, hw1, hw2⟩⟩ := hY
  rw [contract, hv.1.mem_erase_iff] at hv1 hw1
  refine ⟨⟨v, hv1.2, ?_⟩, ⟨w, hw1.2, ?_⟩⟩
  · simp only [rename, hv1.1, ite_false]; exact hv2
  · simp only [rename, hw1.1, ite_false]; exact hw2

/-- A cut that does not separate the contracted edge survives the contraction, with the same
size. -/
private theorem isCut_contract {st : State V} (hv : st.Valid) {e : V × V} (he : e ∈ st.edges)
    {X : V → Bool} (hX : IsCut st X) (hsame : X e.1 = X e.2) :
    IsCut (contract st e) X ∧ cutSize (contract st e).edges X = cutSize st.edges X := by
  obtain ⟨ha, -, hab⟩ := hv.2 e he
  have hren : (fun v => X (rename e.2 e.1 v)) = X := by
    funext v
    by_cases hvb : v = e.2
    · simp [rename, hvb, hsame]
    · simp [rename, hvb]
  refine ⟨?_, by rw [cutSize_contract, hren]⟩
  have hmem : ∀ c, ∀ v ∈ st.verts, X v = c → ∃ w ∈ (contract st e).verts, X w = c := by
    intro c v hv' hc
    by_cases hvb : v = e.2
    · refine ⟨e.1, ?_, by rw [hsame, ← hvb, hc]⟩
      rw [contract, hv.1.mem_erase_iff]; exact ⟨hab, ha⟩
    · refine ⟨v, ?_, hc⟩
      rw [contract, hv.1.mem_erase_iff]; exact ⟨hvb, hv'⟩
  obtain ⟨⟨v, hv1, hv2⟩, ⟨w, hw1, hw2⟩⟩ := hX
  exact ⟨hmem true v hv1 hv2, hmem false w hw1 hw2⟩

/-- **Contraction preserves the minimum cut size.** Let $G$ be a valid multigraph state with
minimum cut size $k$, and let $X$ be a cut of $G$ of size $k$. If $e = (a, b)$ is an edge of $G$
with $X(a) = X(b)$, then the contraction of $G$ along $e$ also has minimum cut size $k$. -/
theorem isMinCut_contract {st : State V} (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    {X : V → Bool} (hX : IsCut st X) (hk : cutSize st.edges X = k) {e : V × V}
    (he : e ∈ st.edges) (hsame : X e.1 = X e.2) : IsMinCut (contract st e) k := by
  obtain ⟨hcut, hsize⟩ := isCut_contract hv he hX hsame
  refine ⟨⟨X, hcut, hsize.trans hk⟩, fun Y hY => ?_⟩
  rw [cutSize_contract]
  exact hmin.2 _ (isCut_lift hv hY)

/-- **Contraction preserves validity and removes one vertex.** If a multigraph $G$ is valid and
$e$ is one of its edges, then the contraction of $G$ along $e$ is valid and has exactly one
vertex fewer than $G$. -/
theorem valid_contract {st : State V} (hv : st.Valid) {e : V × V} (he : e ∈ st.edges) :
    (contract st e).Valid ∧ (contract st e).verts.length = st.verts.length - 1 := by
  obtain ⟨ha, hb, hab⟩ := hv.2 e he
  refine ⟨⟨hv.1.erase _, fun x hx => ?_⟩, List.length_erase_of_mem hb⟩
  simp only [contract, List.mem_filter, List.mem_map, decide_eq_true_eq] at hx
  obtain ⟨⟨y, hy, rfl⟩, hne⟩ := hx
  obtain ⟨hy1, hy2, -⟩ := hv.2 y hy
  have hren : ∀ v ∈ st.verts, rename e.2 e.1 v ∈ st.verts.erase e.2 := by
    intro v hv'
    rw [hv.1.mem_erase_iff]
    by_cases hvb : v = e.2
    · simp only [rename, hvb, ite_true]; exact ⟨hab, ha⟩
    · simp only [rename, hvb, ite_false]; exact ⟨hvb, hv'⟩
  exact ⟨hren _ hy1, hren _ hy2, hne⟩

/-! ## Degrees -/

omit [DecidableEq V] in
private theorem sum_indicator [DecidableEq V] {l : List V} (hnd : l.Nodup) {c : V} (hc : c ∈ l) :
    (l.map fun v => if v = c then (1 : ℕ) else 0).sum = 1 := by
  induction l with
  | nil => exact absurd hc List.not_mem_nil
  | cons x l ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.sum_cons]
      by_cases hxc : x = c
      · subst hxc
        have : (l.map fun v => if v = x then (1 : ℕ) else 0).sum = 0 := by
          rw [List.sum_eq_zero]
          intro n hn
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hn
          have hvx : v ≠ x := by rintro rfl; exact hnd.1 hv
          simp [hvx]
        simp [this]
      · simp only [hxc, ite_false, zero_add]
        exact ih hnd.2 ((List.mem_cons.1 hc).resolve_left (Ne.symm hxc))

private theorem sum_degree_aux (verts : List V) (hnd : verts.Nodup) : ∀ E : List (V × V),
    (∀ e ∈ E, e.1 ∈ verts ∧ e.2 ∈ verts ∧ e.1 ≠ e.2) →
    (verts.map fun v => cutSize E fun x => decide (x = v)).sum = 2 * E.length
  | [], _ => by simp [cutSize]
  | e :: E, hE => by
      obtain ⟨h1, h2, h12⟩ := hE e List.mem_cons_self
      have hsplit : ∀ v, cutSize (e :: E) (fun x => decide (x = v)) =
          cutSize E (fun x => decide (x = v)) +
            ((if v = e.1 then 1 else 0) + (if v = e.2 then 1 else 0)) := by
        intro v
        simp only [cutSize, List.filter_cons]
        by_cases hv1 : v = e.1
        · subst hv1
          simp [Ne.symm h12, h12]
        · by_cases hv2 : v = e.2
          · subst hv2; simp [h12, hv1]
          · simp [hv1, hv2, Ne.symm hv1, Ne.symm hv2]
      simp only [hsplit, List.sum_map_add]
      rw [sum_degree_aux verts hnd E fun x hx => hE x (List.mem_cons_of_mem _ hx),
        sum_indicator hnd h1, sum_indicator hnd h2, List.length_cons]
      omega

/-- **Handshake lemma.** For a valid multigraph $G$, the sum over the vertices $v$ of $G$ of the
number of edges crossing the singleton cut $\{v\}$ equals twice the number of edges of $G$. -/
theorem sum_degree (st : State V) (hv : st.Valid) :
    (st.verts.map fun v => cutSize st.edges fun x => decide (x = v)).sum =
      2 * st.edges.length :=
  sum_degree_aux st.verts hv.1 st.edges hv.2

omit [DecidableEq V] in
private theorem length_mul_le_sum (k : ℕ) (f : V → ℕ) : ∀ l : List V, (∀ v ∈ l, k ≤ f v) →
    l.length * k ≤ (l.map f).sum
  | [], _ => by simp
  | x :: l, h => by
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 := h x List.mem_cons_self
      have h2 := length_mul_le_sum k f l fun v hv => h v (List.mem_cons_of_mem _ hv)
      nlinarith

omit [DecidableEq V] in
/-- **Minimum cut size bounds the number of edges.** Let $G$ be a valid multigraph state with
$n \ge 2$ vertices, $m$ edges (counted with multiplicity) and minimum cut size $k$. Then
$n k \le 2m$: every vertex has degree at least $k$, since its singleton is a cut. -/
theorem card_mul_le_two_mul_edges {st : State V} (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) : st.verts.length * k ≤ 2 * st.edges.length := by
  classical
  rw [← sum_degree st hv]
  refine length_mul_le_sum k _ st.verts fun v hv' => ?_
  refine hmin.2 _ ⟨⟨v, hv', by simp⟩, ?_⟩
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ st.verts, w ≠ v := by
    by_contra hcon
    push Not at hcon
    have : st.verts = List.replicate st.verts.length v :=
      List.eq_replicate_iff.2 ⟨rfl, hcon⟩
    have hnd := hv.1
    rw [this] at hnd
    have := List.nodup_replicate.1 hnd
    omega
  exact ⟨w, hw, by simp [hwv]⟩

/-! ## The success probability -/

/-- **The success probability is nonnegative.** For every natural number $k$, every number $f$
of allowed contractions and every multigraph state $G$, the probability $P_k(f, G)$ that the
contraction process on $G$ returns $k$ satisfies $0 \le P_k(f, G)$. -/
theorem successProb_nonneg (k : ℕ) : ∀ (fuel : ℕ) (st : State V), 0 ≤ successProb k fuel st
  | 0, st => by
      unfold successProb
      split_ifs <;> simp
  | fuel + 1, st => by
      unfold successProb
      split_ifs
      · simp
      · simp
      · refine div_nonneg (List.sum_nonneg fun x hx => ?_) (Nat.cast_nonneg _)
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
        exact successProb_nonneg k fuel _

/-- **The success probability is at most one.** For every natural number $k$, every number of
allowed contractions and every multigraph $G$, the probability that the contraction process on
$G$ returns $k$ is at most $1$. -/
theorem successProb_le_one (k : ℕ) : ∀ (fuel : ℕ) (st : State V), successProb k fuel st ≤ 1
  | 0, st => by
      unfold successProb
      split_ifs <;> simp
  | fuel + 1, st => by
      unfold successProb
      split_ifs with h
      · simp
      · simp
      · push Not at h
        have hm : (0 : ℚ) < st.edges.length := by exact_mod_cast List.length_pos_of_ne_nil h.2
        rw [div_le_one hm]
        have key : ∀ E : List (V × V),
            (E.map fun e => successProb k fuel (contract st e)).sum ≤ E.length := by
          intro E
          induction E with
          | nil => simp
          | cons e E ih =>
              simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
                Nat.cast_one]
              have := successProb_le_one k fuel (contract st e)
              linarith
        exact key st.edges

omit [DecidableEq V] in
/-- When the process stops (two vertices left, or no edges), the remaining edges are exactly a
minimum cut. -/
private theorem edges_length_eq {st : State V} (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) (hstop : st.verts.length ≤ 2 ∨ st.edges = []) :
    st.edges.length = k := by
  obtain ⟨X, hX, hk⟩ := hmin.1
  rcases hstop with h2 | hE
  · rw [← hk, cutSize, List.filter_eq_self.2]
    intro e he
    obtain ⟨h1, h2', h12⟩ := hv.2 e he
    match hvs : st.verts, hn, h2, hX, hv.1 with
    | [a, b], _, _, hX, hnd =>
        rw [hvs] at h1 h2'
        obtain ⟨⟨v, hv1, hv2⟩, ⟨w, hw1, hw2⟩⟩ := hX
        rw [hvs] at hv1 hw1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2' hv1 hw1
        have hab : X a ≠ X b := by
          rcases hv1 with rfl | rfl <;> rcases hw1 with rfl | rfl <;> simp_all
        rcases h1 with h1 | h1 <;> rcases h2' with h2' | h2'
        · exact absurd (h1.trans h2'.symm) h12
        · rw [h1, h2']; simpa using hab
        · rw [h1, h2']; simpa using Ne.symm hab
        · exact absurd (h1.trans h2'.symm) h12
  · rw [← hk, hE]; rfl

omit [DecidableEq V] in
private theorem filter_length_mul_le_sum (f : V × V → ℚ) (p : V × V → Bool) (c : ℚ) :
    ∀ E : List (V × V), (∀ e ∈ E, 0 ≤ f e) → (∀ e ∈ E, p e = true → c ≤ f e) →
    ((E.filter p).length : ℚ) * c ≤ (E.map f).sum
  | [], _, _ => by simp
  | e :: E, hf, hc => by
      have ih := filter_length_mul_le_sum f p c E (fun x hx => hf x (List.mem_cons_of_mem _ hx))
        (fun x hx => hc x (List.mem_cons_of_mem _ hx))
      have h0 := hf e List.mem_cons_self
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      by_cases hp : p e = true
      · simp only [hp, ite_true, List.length_cons, Nat.cast_add, Nat.cast_one]
        have := hc e List.mem_cons_self hp
        linarith
      · simp only [hp, Bool.false_eq_true, ite_false]
        linarith

private theorem successProb_ge_aux (k : ℕ) : ∀ (fuel : ℕ) (st : State V), st.Valid →
    IsMinCut st k → 2 ≤ st.verts.length → st.verts.length ≤ fuel + 2 →
    2 / ((st.verts.length : ℚ) * (st.verts.length - 1)) ≤ successProb k fuel st
  | 0, st, hv, hmin, hn, hfuel => by
      have hlen := edges_length_eq hv hmin hn (Or.inl (by omega))
      have h2 : st.verts.length = 2 := by omega
      rw [successProb]
      simp [hlen, h2]
      norm_num
  | fuel + 1, st, hv, hmin, hn, hfuel => by
      by_cases hstop : st.verts.length ≤ 2 ∨ st.edges = []
      · have hlen := edges_length_eq hv hmin hn hstop
        rw [successProb]
        simp only [hstop, hlen, ite_true]
        have hN : (2 : ℚ) ≤ st.verts.length := by exact_mod_cast hn
        rw [div_le_one (by nlinarith)]
        nlinarith
      · rw [successProb]
        simp only [hstop, ite_false]
        push Not at hstop
        obtain ⟨hn3, hE⟩ := hstop
        obtain ⟨X, hX, hk⟩ := hmin.1
        have hm : 0 < st.edges.length := List.length_pos_of_ne_nil hE
        set c : ℚ := 2 / (((st.verts.length - 1 : ℕ) : ℚ) * (((st.verts.length - 1 : ℕ) : ℚ) - 1))
          with hc
        have hgood : ∀ e ∈ st.edges, (!(X e.1 != X e.2)) = true →
            c ≤ successProb k fuel (contract st e) := by
          intro e he hne
          have hsame : X e.1 = X e.2 := by simpa using hne
          obtain ⟨hv', hlen'⟩ := valid_contract hv he
          have := successProb_ge_aux k fuel (contract st e) hv'
            (isMinCut_contract hv hmin hX hk he hsame) (by omega) (by omega)
          rwa [hlen'] at this
        have hsum := filter_length_mul_le_sum (fun e => successProb k fuel (contract st e))
          (fun e => !(X e.1 != X e.2)) c st.edges (fun e _ => successProb_nonneg k fuel _) hgood
        have hkm : k ≤ st.edges.length := by
          rw [← hk, cutSize]; exact List.length_filter_le _ _
        have hcount : (st.edges.filter fun e => !(X e.1 != X e.2)).length =
            st.edges.length - k := by
          have := List.length_eq_length_filter_add (l := st.edges) (fun e => X e.1 != X e.2)
          rw [cutSize] at hk
          omega
        have hdeg := card_mul_le_two_mul_edges hv hmin hn
        rw [hcount] at hsum
        rw [le_div_iff₀ (by exact_mod_cast hm)]
        refine le_trans ?_ hsum
        -- arithmetic: `2 m / (n (n - 1)) ≤ (m - k) · 2 / ((n - 1) (n - 2))` from `n k ≤ 2 m`
        have hN : (3 : ℚ) ≤ st.verts.length := by exact_mod_cast hn3
        have hcast1 : ((st.verts.length - 1 : ℕ) : ℚ) = st.verts.length - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have hcast2 : ((st.edges.length - k : ℕ) : ℚ) = st.edges.length - k := by
          rw [Nat.cast_sub hkm]
        have hdeg' : (st.verts.length : ℚ) * k ≤ 2 * st.edges.length := by exact_mod_cast hdeg
        rw [hc, hcast1, hcast2]
        set N : ℚ := (st.verts.length : ℚ)
        set M : ℚ := (st.edges.length : ℚ)
        have h1 : 0 < N - 1 := by linarith
        have h2 : 0 < N - 1 - 1 := by linarith
        have hN0 : 0 < N := by linarith
        rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hN0 h1, mul_pos h1 h2]

/-- **Karger's bound.** Let $G$ be a valid multigraph with $n \ge 2$ vertices and minimum cut
size $k$. Then the contraction process on $G$, with $n$ contractions allowed, returns $k$ with
probability at least $2 / (n(n-1))$. -/
theorem successProb_ge (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) :
    2 / ((st.verts.length : ℚ) * (st.verts.length - 1)) ≤
      successProb k st.verts.length st :=
  successProb_ge_aux k _ st hv hmin hn (by omega)

/-! ## Amplification -/

/-- **Success probability of repeated runs.** For a multigraph $G$ with $n$ vertices and
natural numbers $k$ and $t$, let $p$ be the probability that one run of the contraction process
on $G$, with $n$ contractions allowed, returns $k$. The repeated success probability is
$1 - (1 - p)^t$, the probability that at least one of $t$ independent runs returns $k$. -/
def repeatSuccessProb (k t : ℕ) (st : State V) : ℚ :=
  1 - (1 - successProb k st.verts.length st) ^ t

private theorem one_sub_inv_pow_le_half {N : ℕ} (hN : 1 ≤ N) :
    (1 - 1 / (N : ℚ)) ^ N ≤ 1 / 2 := by
  have hN' : (1 : ℚ) ≤ N := by exact_mod_cast hN
  set x : ℚ := 1 / N with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by linarith)]; exact hN'
  have hNx : (N : ℚ) * x = 1 := by rw [hx]; field_simp
  have h1 : 2 ≤ (1 + x) ^ N := by
    have := one_add_mul_le_pow (a := x) (by linarith) N
    linarith
  have h2 : (1 - x) ^ N * (1 + x) ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 0 ≤ (1 - x) ^ N := pow_nonneg (by linarith) N
  nlinarith

/-- With `N = n (n - 1) / 2`, one run fails with probability `q ≤ 1 - 1/N`, so `N` runs all fail
with probability `q ^ N ≤ 1 / 2`. -/
private theorem fail_pow_le_half (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) :
    ∃ N : ℕ, st.verts.length * (st.verts.length - 1) = N + N ∧
      0 ≤ 1 - successProb k st.verts.length st ∧ 1 - successProb k st.verts.length st ≤ 1 ∧
      (1 - successProb k st.verts.length st) ^ N ≤ 1 / 2 := by
  have hp := successProb_ge st hv hmin hn
  have hp1 := successProb_le_one k st.verts.length st
  have hp0 := successProb_nonneg k st.verts.length st
  obtain ⟨N, hNeq⟩ := Nat.even_mul_pred_self st.verts.length
  have hN : 1 ≤ N := by
    have : 2 ≤ st.verts.length * (st.verts.length - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ st.verts.length * (st.verts.length - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have hcast : ((st.verts.length : ℚ) * (st.verts.length - 1)) = 2 * N := by
    have : ((st.verts.length * (st.verts.length - 1) : ℕ) : ℚ) = ((N + N : ℕ) : ℚ) := by
      rw [hNeq]
    push_cast [Nat.cast_sub (by omega : 1 ≤ st.verts.length)] at this
    linarith
  rw [hcast] at hp
  have hp' : 1 / (N : ℚ) ≤ successProb k st.verts.length st := by
    have : (2 : ℚ) / (2 * N) = 1 / N := by field_simp
    linarith
  set q := 1 - successProb k st.verts.length st with hq
  have hq0 : 0 ≤ q := by linarith
  have hq1 : q ≤ 1 - 1 / (N : ℚ) := by linarith
  have hqN : q ^ N ≤ (1 - 1 / (N : ℚ)) ^ N := pow_le_pow_left₀ hq0 hq1 N
  exact ⟨N, hNeq, hq0, by linarith, hqN.trans (one_sub_inv_pow_le_half hN)⟩

/-- **Repeating Karger's algorithm succeeds with probability at least one half.** Let $G$ be a
valid multigraph state with $n \ge 2$ vertices and minimum cut size $k$, and let $t$ be a natural
number with $n(n-1) \le 2t$. Then the probability that at least one of $t$ independent runs of
the contraction process returns $k$ is at least $1/2$. -/
theorem repeatSuccessProb_ge_half (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) {t : ℕ} (ht : st.verts.length * (st.verts.length - 1) ≤ 2 * t) :
    1 / 2 ≤ repeatSuccessProb k t st := by
  obtain ⟨N, hNeq, hq0, hq1, hqN⟩ := fail_pow_le_half st hv hmin hn
  have hqt := pow_le_pow_of_le_one hq0 hq1 (show N ≤ t by omega)
  unfold repeatSuccessProb
  linarith

/-- **Amplification with high probability.** Let $G$ be a valid multigraph with $n \ge 2$
vertices and minimum cut size $k$, and let $c$ and $t$ be natural numbers with
$c \cdot n(n-1) \le 2t$. Then the probability that at least one of $t$ independent runs of the
contraction process on $G$ returns $k$ is at least $1 - (1/2)^c$. -/
theorem repeatSuccessProb_ge (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) {c t : ℕ}
    (ht : c * (st.verts.length * (st.verts.length - 1)) ≤ 2 * t) :
    1 - (1 / 2 : ℚ) ^ c ≤ repeatSuccessProb k t st := by
  obtain ⟨N, hNeq, hq0, hq1, hqN⟩ := fail_pow_le_half st hv hmin hn
  set q := 1 - successProb k st.verts.length st
  have hct : N * c ≤ t := by rw [hNeq] at ht; nlinarith
  have h1 : q ^ t ≤ q ^ (N * c) := pow_le_pow_of_le_one hq0 hq1 hct
  have h2 : q ^ (N * c) ≤ (1 / 2 : ℚ) ^ c := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hq0 N) hqN c
  unfold repeatSuccessProb
  linarith

/-- **Karger's algorithm succeeds with high probability.** Let $G$ be a valid multigraph with
$n \ge 2$ vertices and minimum cut size $k$, and let $t$ be a natural number with
$\lceil \log_2 n \rceil \cdot n(n-1) \le 2t$. Then the probability that at least one of $t$
independent runs of the contraction process on $G$ returns $k$ is at least $1 - 1/n$.

Thus $O(n^2 \log n)$ runs find the minimum cut size with high probability. -/
theorem repeatSuccessProb_ge_one_sub_inv (st : State V) (hv : st.Valid) {k : ℕ}
    (hmin : IsMinCut st k) (hn : 2 ≤ st.verts.length) {t : ℕ}
    (ht : Nat.clog 2 st.verts.length * (st.verts.length * (st.verts.length - 1)) ≤ 2 * t) :
    1 - 1 / (st.verts.length : ℚ) ≤ repeatSuccessProb k t st := by
  refine le_trans ?_ (repeatSuccessProb_ge st hv hmin hn ht)
  have hle : st.verts.length ≤ 2 ^ Nat.clog 2 st.verts.length := Nat.le_pow_clog (by norm_num) _
  have hle' : (st.verts.length : ℚ) ≤ 2 ^ Nat.clog 2 st.verts.length := by exact_mod_cast hle
  have hpos : (0 : ℚ) < st.verts.length := by exact_mod_cast (show 0 < st.verts.length by omega)
  have : (1 / 2 : ℚ) ^ Nat.clog 2 st.verts.length ≤ 1 / (st.verts.length : ℚ) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le hpos hle'
  linarith

/-! ## Counting minimum cuts -/

instance (st : State V) (X : V → Bool) : Decidable (IsCut st X) := by
  unfold IsCut; infer_instance

/-- **Probability that a run outputs a given cut.** For a map $X$ from vertices to booleans, a
fuel bound $f$ and a multigraph $G$, this is the probability that the contraction process on $G$
(contract an edge chosen uniformly at random, counted with multiplicity, while more than two
vertices and at least one edge remain, making at most $f$ contractions) never contracts an edge
whose endpoints $X$ separates and ends with exactly two vertices on which $X$ takes both values.

Explicitly: if $f = 0$, or $G$ has at most two vertices, or $G$ has no edges, the value is $1$
when $G$ has exactly two vertices and $X$ is a cut of $G$, and $0$ otherwise. Otherwise it is the
average over the edges $e$ of $G$, counted with multiplicity, of the value for fuel $f - 1$ on
the contraction of $G$ along $e$ when $X$ agrees on the two endpoints of $e$, and of $0$ when it
does not. -/
def surviveProb (X : V → Bool) : ℕ → State V → ℚ
  | 0, st => if st.verts.length = 2 ∧ IsCut st X then 1 else 0
  | fuel + 1, st =>
      if st.verts.length ≤ 2 ∨ st.edges = [] then
        (if st.verts.length = 2 ∧ IsCut st X then 1 else 0)
      else
        (st.edges.map fun e =>
            if X e.1 = X e.2 then surviveProb X fuel (contract st e) else 0).sum /
          st.edges.length

/-- **Cuts distinct as partitions.** Two maps $X, Y$ from vertices to booleans are distinct on a
list of vertices $S$ when some $v \in S$ has $X(v) \ne Y(v)$ and some $w \in S$ has
$X(w) = Y(w)$; so on $S$ neither cut is the other or its complement. -/
def DistinctOn (S : List V) (X Y : V → Bool) : Prop :=
  (∃ v ∈ S, X v ≠ Y v) ∧ ∃ v ∈ S, X v = Y v

theorem surviveProb_nonneg (X : V → Bool) :
    ∀ (fuel : ℕ) (st : State V), 0 ≤ surviveProb X fuel st
  | 0, st => by unfold surviveProb; split_ifs <;> norm_num
  | fuel + 1, st => by
      unfold surviveProb
      split_ifs
      · norm_num
      · norm_num
      · refine div_nonneg (List.sum_nonneg fun x hx => ?_) (Nat.cast_nonneg _)
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
        split_ifs
        · exact surviveProb_nonneg X fuel _
        · exact le_rfl

private theorem surviveProb_ge_aux (X : V → Bool) (k : ℕ) (hk1 : 1 ≤ k) :
    ∀ (fuel : ℕ) (st : State V), st.Valid → IsMinCut st k → IsCut st X →
      cutSize st.edges X = k → 2 ≤ st.verts.length → st.verts.length ≤ fuel + 2 →
      2 / ((st.verts.length : ℚ) * (st.verts.length - 1)) ≤ surviveProb X fuel st
  | 0, st, _, _, hX, _, hn, hfuel => by
      have h2 : st.verts.length = 2 := by omega
      rw [surviveProb, ite_eq_left_iff.2 fun h => absurd ⟨h2, hX⟩ h, h2]
      norm_num
  | fuel + 1, st, hv, hmin, hX, hk, hn, hfuel => by
      have hE : st.edges ≠ [] := by
        intro h
        rw [h] at hk
        simp [cutSize] at hk
        omega
      by_cases hstop : st.verts.length ≤ 2 ∨ st.edges = []
      · have h2 : st.verts.length = 2 := by
          rcases hstop with h | h
          · omega
          · exact absurd h hE
        rw [surviveProb, ite_eq_left_iff.2 fun h => absurd hstop h,
          ite_eq_left_iff.2 fun h => absurd ⟨h2, hX⟩ h, h2]
        norm_num
      · rw [surviveProb, ite_eq_right_iff.2 fun h => absurd h hstop]
        push Not at hstop
        obtain ⟨hn3, -⟩ := hstop
        have hm : 0 < st.edges.length := List.length_pos_of_ne_nil hE
        set c : ℚ := 2 / (((st.verts.length - 1 : ℕ) : ℚ) * (((st.verts.length - 1 : ℕ) : ℚ) - 1))
          with hc
        have hgood : ∀ e ∈ st.edges, (!(X e.1 != X e.2)) = true →
            c ≤ (fun e => if X e.1 = X e.2 then surviveProb X fuel (contract st e) else 0) e := by
          intro e he hne
          have hsame : X e.1 = X e.2 := by simpa using hne
          simp only [hsame, ite_true]
          obtain ⟨hv', hlen'⟩ := valid_contract hv he
          obtain ⟨hX', hk'⟩ := isCut_contract hv he hX hsame
          have := surviveProb_ge_aux X k hk1 fuel (contract st e) hv'
            (isMinCut_contract hv hmin hX hk he hsame) hX' (hk'.trans hk) (by omega) (by omega)
          rwa [hlen'] at this
        have hsum := filter_length_mul_le_sum
          (fun e => if X e.1 = X e.2 then surviveProb X fuel (contract st e) else 0)
          (fun e => !(X e.1 != X e.2)) c st.edges
          (fun e _ => by
            split_ifs
            · exact surviveProb_nonneg X fuel _
            · exact le_rfl)
          hgood
        have hkm : k ≤ st.edges.length := by
          rw [← hk, cutSize]; exact List.length_filter_le _ _
        have hcount : (st.edges.filter fun e => !(X e.1 != X e.2)).length =
            st.edges.length - k := by
          have := List.length_eq_length_filter_add (l := st.edges) (fun e => X e.1 != X e.2)
          rw [cutSize] at hk
          omega
        have hdeg := card_mul_le_two_mul_edges hv hmin hn
        rw [hcount] at hsum
        rw [le_div_iff₀ (by exact_mod_cast hm)]
        refine le_trans ?_ hsum
        have hN : (3 : ℚ) ≤ st.verts.length := by exact_mod_cast hn3
        have hcast1 : ((st.verts.length - 1 : ℕ) : ℚ) = st.verts.length - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have hcast2 : ((st.edges.length - k : ℕ) : ℚ) = st.edges.length - k := by
          rw [Nat.cast_sub hkm]
        have hdeg' : (st.verts.length : ℚ) * k ≤ 2 * st.edges.length := by exact_mod_cast hdeg
        rw [hc, hcast1, hcast2]
        set N : ℚ := (st.verts.length : ℚ)
        set M : ℚ := (st.edges.length : ℚ)
        have h1 : 0 < N - 1 := by linarith
        have h2 : 0 < N - 1 - 1 := by linarith
        have hN0 : 0 < N := by linarith
        rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hN0 h1, mul_pos h1 h2]

/-- **Each minimum cut survives with probability at least $2/(n(n-1))$.** Let $G$ be a valid
multigraph with $n \ge 2$ vertices whose minimum cut size $k$ is at least $1$, and let $X$ be a
cut of $G$ with exactly $k$ crossing edges. Then the probability that the contraction process on
$G$, allowed up to $n$ contractions, outputs the cut $X$ is at least $2/(n(n-1))$. -/
theorem surviveProb_ge (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hk1 : 1 ≤ k) {X : V → Bool} (hX : IsCut st X) (hk : cutSize st.edges X = k)
    (hn : 2 ≤ st.verts.length) :
    2 / ((st.verts.length : ℚ) * (st.verts.length - 1)) ≤
      surviveProb X st.verts.length st :=
  surviveProb_ge_aux X k hk1 _ st hv hmin hX hk hn (by omega)

omit [DecidableEq V] in
/-- Two cuts of a two-vertex state are equal or complementary. -/
private theorem not_distinctOn_of_two {S : List V} (h2 : S.length = 2) {X Y : V → Bool}
    (hX : (∃ v ∈ S, X v = true) ∧ ∃ v ∈ S, X v = false)
    (hY : (∃ v ∈ S, Y v = true) ∧ ∃ v ∈ S, Y v = false) : ¬ DistinctOn S X Y := by
  match S, h2 with
  | [a, b], _ =>
      obtain ⟨⟨v₁, hv₁, hX₁⟩, ⟨v₂, hv₂, hX₂⟩⟩ := hX
      obtain ⟨⟨w₁, hw₁, hY₁⟩, ⟨w₂, hw₂, hY₂⟩⟩ := hY
      rintro ⟨⟨u, hu, hne⟩, ⟨u', hu', heq⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv₁ hv₂ hw₁ hw₂ hu hu'
      rcases hv₁ with rfl | rfl <;> rcases hv₂ with rfl | rfl <;> rcases hw₁ with rfl | rfl <;>
        rcases hw₂ with rfl | rfl <;> rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;>
        simp_all

omit [DecidableEq V] in
private theorem sum_ite_eq_sum_filter (p : (V → Bool) → Prop) [DecidablePred p]
    (f : (V → Bool) → ℚ) : ∀ F : List (V → Bool),
      (F.map fun X => if p X then f X else 0).sum = ((F.filter fun X => decide (p X)).map f).sum
  | [] => rfl
  | X :: F => by
      by_cases hX : p X <;> simp [hX, sum_ite_eq_sum_filter p f F]

private theorem sum_comm_div {α β : Type*} (h : α → β → ℚ) (m : ℚ) :
    ∀ (F : List α) (E : List β),
      (F.map fun X => (E.map (h X)).sum / m).sum =
        (E.map fun e => (F.map fun X => h X e).sum).sum / m
  | [], E => by simp
  | X :: F, E => by
      simp only [List.map_cons, List.sum_cons, sum_comm_div h m F E, List.sum_map_add, add_div]

/-- **Survival probabilities of distinct cuts sum to at most one.** Let $G$ be a valid multigraph
with vertex list $S$, let $f$ be a number of allowed contractions, and let $X_1, \dots, X_m$ be
Boolean functions on the vertex type that are pairwise distinct as partitions of $S$. Then the
probabilities that the contraction process on $G$, with $f$ contractions allowed, outputs
$X_1, \dots, X_m$ add up to at most $1$.

The survival events are disjoint: a run outputs at most one partition. -/
theorem sum_surviveProb_le_one : ∀ (fuel : ℕ) (st : State V) (F : List (V → Bool)),
    st.Valid → F.Pairwise (DistinctOn st.verts) →
      (F.map fun X => surviveProb X fuel st).sum ≤ 1 := by
  -- at the end, at most one of the cuts separates the two remaining vertices
  have base : ∀ (st : State V) (F : List (V → Bool)), F.Pairwise (DistinctOn st.verts) →
      (F.map fun X => if st.verts.length = 2 ∧ IsCut st X then (1 : ℚ) else 0).sum ≤ 1 := by
    intro st F hF
    induction F with
    | nil => simp
    | cons X F ih =>
        rw [List.pairwise_cons] at hF
        simp only [List.map_cons, List.sum_cons]
        by_cases hX : st.verts.length = 2 ∧ IsCut st X
        · rw [ite_eq_left_iff.2 fun h => absurd hX h]
          have hzero : (F.map fun Y => if st.verts.length = 2 ∧ IsCut st Y then (1 : ℚ) else 0)
              = F.map fun _ => 0 := by
            refine List.map_congr_left fun Y hY => ite_eq_right_iff.2 fun hY' => ?_
            exact (not_distinctOn_of_two hX.1 hX.2 hY'.2 (hF.1 Y hY)).elim
          rw [hzero]
          simp
        · rw [ite_eq_right_iff.2 fun h => absurd h hX, zero_add]
          exact ih hF.2
  intro fuel
  induction fuel with
  | zero => intro st F _ hF; exact base st F hF
  | succ fuel ih =>
      intro st F hv hF
      simp only [surviveProb]
      by_cases hstop : st.verts.length ≤ 2 ∨ st.edges = []
      · simp only [hstop, ite_true]
        exact base st F hF
      · simp only [hstop, ite_false]
        push Not at hstop
        have hm : (0 : ℚ) < st.edges.length := by
          exact_mod_cast List.length_pos_of_ne_nil hstop.2
        rw [sum_comm_div, div_le_one hm]
        -- each edge contributes at most `1`
        have hle : ∀ e ∈ st.edges, (F.map fun X =>
            if X e.1 = X e.2 then surviveProb X fuel (contract st e) else 0).sum ≤ 1 := by
          intro e he
          obtain ⟨ha, -, hab⟩ := hv.2 e he
          rw [sum_ite_eq_sum_filter (fun X => X e.1 = X e.2)]
          refine ih (contract st e) _ (valid_contract hv he).1 ?_
          refine (hF.filter _).imp_of_mem fun {X Y} hXm hYm hXY => ?_
          simp only [List.mem_filter, decide_eq_true_eq] at hXm hYm
          have hmem : ∀ v ∈ st.verts, ∃ w ∈ (contract st e).verts, X w = X v ∧ Y w = Y v := by
            intro v hv'
            by_cases hvb : v = e.2
            · refine ⟨e.1, ?_, by rw [hvb, hXm.2], by rw [hvb, hYm.2]⟩
              rw [contract, hv.1.mem_erase_iff]; exact ⟨hab, ha⟩
            · refine ⟨v, ?_, rfl, rfl⟩
              rw [contract, hv.1.mem_erase_iff]; exact ⟨hvb, hv'⟩
          obtain ⟨⟨u, hu, hne⟩, ⟨u', hu', heq⟩⟩ := hXY
          obtain ⟨w, hw, hw1, hw2⟩ := hmem u hu
          obtain ⟨w', hw', hw1', hw2'⟩ := hmem u' hu'
          exact ⟨⟨w, hw, by rw [hw1, hw2]; exact hne⟩, ⟨w', hw', by rw [hw1', hw2']; exact heq⟩⟩
        calc (st.edges.map fun e => (F.map fun X =>
              if X e.1 = X e.2 then surviveProb X fuel (contract st e) else 0).sum).sum
            ≤ (st.edges.map fun _ => (1 : ℚ)).sum := List.sum_le_sum fun e he => hle e he
          _ = st.edges.length := by simp

omit [DecidableEq V] in
/-- **At most $n(n-1)/2$ minimum cuts** (Karger; Kleinberg and Tardos, Section 13.2). Let $G$ be a
valid multigraph with $n \ge 2$ vertices whose minimum cut size $k$ is at least $1$. If
$X_1, \dots, X_m$ are cuts of $G$, each with exactly $k$ crossing edges, that are pairwise
distinct as partitions of the vertices of $G$, then $2m \le n(n-1)$, that is, $m \le n(n-1)/2$.

Each of these cuts is output by a run of the contraction process with probability at least
$2/(n(n-1))$, and the runs that output distinct partitions are disjoint. -/
theorem two_mul_length_minCuts_le (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hk1 : 1 ≤ k) (hn : 2 ≤ st.verts.length) (F : List (V → Bool))
    (hF : ∀ X ∈ F, IsCut st X ∧ cutSize st.edges X = k) (hd : F.Pairwise (DistinctOn st.verts)) :
    2 * F.length ≤ st.verts.length * (st.verts.length - 1) := by
  classical
  set N : ℚ := (st.verts.length : ℚ) with hN
  have hN2 : (2 : ℚ) ≤ N := by rw [hN]; exact_mod_cast hn
  set c : ℚ := 2 / (N * (N - 1)) with hc
  have hlow : ∀ X ∈ F, c ≤ surviveProb X st.verts.length st := fun X hX =>
    surviveProb_ge st hv hmin hk1 (hF X hX).1 (hF X hX).2 hn
  have hsum : (F.length : ℚ) * c ≤ (F.map fun X => surviveProb X st.verts.length st).sum := by
    clear hd hF
    induction F with
    | nil => simp
    | cons X F ih =>
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
        have := hlow X List.mem_cons_self
        have := ih fun Y hY => hlow Y (List.mem_cons_of_mem _ hY)
        linarith
  have hle := sum_surviveProb_le_one st.verts.length st F hv hd
  have hpos : 0 < N * (N - 1) := by nlinarith
  have hfin : (F.length : ℚ) * 2 ≤ N * (N - 1) := by
    have := hsum.trans hle
    rw [hc, mul_div_assoc', div_le_one hpos] at this
    exact this
  have hcast : ((st.verts.length * (st.verts.length - 1) : ℕ) : ℚ) = N * (N - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have : ((2 * F.length : ℕ) : ℚ) ≤ ((st.verts.length * (st.verts.length - 1) : ℕ) : ℚ) := by
    rw [hcast]; push_cast; linarith
  exact_mod_cast this

end Cslib.Algorithms.Lean.Karger
