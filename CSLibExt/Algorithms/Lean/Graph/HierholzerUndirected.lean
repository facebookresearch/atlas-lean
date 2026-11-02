/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.Hierholzer
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Relation

/-!
# Euler circuits in undirected multigraphs by Hierholzer's algorithm

Hierholzer's algorithm for undirected multigraphs (C. Hierholzer, 1873; Euler's theorem: a
connected multigraph has an Euler circuit iff every vertex has even degree, and an Euler path
between `s ≠ t` iff exactly `s` and `t` have odd degree). The directed version is
`Hierholzer.lean`; here an edge can be traversed in either direction, and traversing it removes it
for both endpoints.

The multigraph is an edge list `E : List (V × V)`, each pair one undirected edge (repeated pairs
are parallel edges, `(v, v)` is a loop). `udeg E x` is the degree of `x` (a loop counts twice).
From `v`, `uvisit` takes the first remaining edge at `v`, removes it, recurses at its other
endpoint, and then continues at `v`; when no edge is left at `v` it emits `v`.

* `IsUEulerPath E s t W`: `W` starts at `s`, ends at `t`, and its steps, as unordered pairs, are a
  permutation of the edges.
* `uhierholzer_isUEulerPath`: if exactly `s` and `t` have odd degree (`EvenExcept E s t`; every
  degree is even when `s = t`) and every edge starts at a vertex reachable from `s`
  (`UReach`), `uhierholzer E s` is an Euler path from `s` to `t`; `uhierholzer_isUEulerCircuit`
  is the case `s = t`.
* `uhierholzer_trail`: without the reachability hypothesis, the result is still a walk from `s` to
  `t` whose steps are a sub-multiset of the edges.

The proof follows `Hierholzer.lean`: a call at `v` on a remaining multigraph whose odd-degree
vertices are exactly `v` and `t` (none when `v = t`) emits a walk from `v` to `t` and leaves a
remainder of even degrees in which the walk's vertices have no edges (`uvisit_spec`).

## Cost model

One unit per edge traversal (removing an edge from the remaining list). Finding the first edge at
`v` and emitting a vertex are free, as with per-vertex incidence lists in which both copies of an
edge are removed together. A run whose edges are all reachable costs exactly `|E|`
(`uhierholzer_time`). The executable state is a list, which models those incidence lists but whose
own scans are not constant time, so the bound is in the model.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Hierholzer

open Cslib.Algorithms.Lean TimeM

universe u

variable {V : Type u} [DecidableEq V]

/-- **Unordered edge of an ordered pair.** The ordered pair $(a, b)$ of vertices, viewed as the
unordered pair $\{a, b\}$, so that $(a, b)$ and $(b, a)$ give the same unordered edge. -/
def usym (e : V × V) : Sym2 V := s(e.1, e.2)

/-- **Degree in an undirected edge list.** For a finite list $R$ of edges of an undirected
multigraph, each given as a pair $(a, b)$, the degree of a vertex $x$ is the number of edges in
$R$ whose first component is $x$ plus the number whose second component is $x$; parallel edges
count separately and a loop $(x, x)$ counts twice. -/
def udeg (R : List (V × V)) (x : V) : ℕ := (R.map Prod.fst).count x + (R.map Prod.snd).count x

/-- **Degree parity condition for two endpoints.** For a finite list $R$ of edges of an
undirected multigraph and vertices $v$, $t$, the condition holds when for every vertex $x$ the
number $\deg_R(x) + [x = v] + [x = t]$ is even, where $\deg_R$ is the degree in $R$ (a loop counts
twice) and $[P]$ is $1$ if $P$ holds and $0$ otherwise. Thus if $v \ne t$, exactly $v$ and $t$
have odd degree, and if $v = t$, every degree is even. -/
def EvenExcept (R : List (V × V)) (v t : V) : Prop :=
  ∀ x, (udeg R x + (if x = v then 1 else 0) + (if x = t then 1 else 0)) % 2 = 0

/-- **Reachability in an undirected multigraph.** For a list $E$ of edges (ordered pairs of
vertices), a vertex $x$ is reachable from a vertex $s$ when there are vertices
$s = v_0, v_1, \dots, v_n = x$ with $n \ge 0$ such that for each $i < n$, $(v_i, v_{i+1})$ or
$(v_{i+1}, v_i)$ belongs to $E$. -/
def UReach (E : List (V × V)) (s x : V) : Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) s x

/-- **Euler path in an undirected multigraph.** For a finite list $E$ of edges of an undirected
multigraph and vertices $s$, $t$, a sequence of vertices $W = (w_0, \dots, w_n)$ is an Euler path
of $E$ from $s$ to $t$ when $w_0 = s$, $w_n = t$, and the multiset of unordered pairs
$\{w_{i-1}, w_i\}$ for $1 \le i \le n$ equals the multiset of the edges of $E$ taken as unordered
pairs. Thus every edge is traversed exactly once, in either direction. -/
def IsUEulerPath (E : List (V × V)) (s t : V) (W : List V) : Prop :=
  W.head? = some s ∧ W.getLast? = some t ∧ ((walkEdges W).map usym).Perm (E.map usym)

instance (E : List (V × V)) (s t : V) (W : List V) : Decidable (IsUEulerPath E s t W) := by
  unfold IsUEulerPath; infer_instance

instance [Fintype V] (R : List (V × V)) (v t : V) : Decidable (EvenExcept R v t) := by
  unfold EvenExcept; infer_instance

/-- **Other endpoint of an edge.** For an edge $e = (a, b)$ and a vertex $v$, the other endpoint
of $e$ at $v$ is $b$ if $a = v$, and $a$ otherwise; in particular a loop $(v, v)$ gives $v$. -/
def otherEnd (e : V × V) (v : V) : V := if e.1 = v then e.2 else e.1

/-- **Undirected Hierholzer recursion.** The recursion takes a fuel $f \in \mathbb{N}$, a vertex
$v$, a list $R$ of remaining edges and an accumulator list $A$ of vertices, and returns a list of
vertices and a list of remaining edges. With fuel $0$ it returns $A$ and $R$ unchanged. With fuel
$f + 1$: if no edge of $R$ has $v$ as an endpoint, it returns $v$ prepended to $A$, together with
$R$; otherwise, with $e$ the first such edge, it removes $e$ from $R$ at a cost of one unit,
recurses with fuel $f$ from the other endpoint of $e$ at $v$ on the shortened list with
accumulator $A$, obtaining a vertex list $A'$ and remaining edges $R'$, and then recurses with fuel
$f$ from $v$ on $R'$ with accumulator $A'$. -/
def uvisit : ℕ → V → List (V × V) → List V → TimeM ℕ (List V × List (V × V))
  | 0, _, R, acc => pure (acc, R)
  | fuel + 1, v, R, acc =>
      match R.find? (fun e => e.1 = v ∨ e.2 = v) with
      | none => pure (v :: acc, R)
      | some e => do
          ✓
          let r ← uvisit fuel (otherEnd e v) (R.erase e) acc
          uvisit fuel v r.2 r.1

/-- **Undirected Hierholzer's algorithm.** Given a list $E$ of undirected edges (ordered pairs of
vertices) and a start vertex $s$, run the undirected Hierholzer recursion from $s$ on $E$ with an
empty accumulator and fuel $|E| + 1$, and return the list of emitted vertices; its cost is the
cost of that recursion. -/
def uhierholzer (E : List (V × V)) (s : V) : TimeM ℕ (List V) := do
  let r ← uvisit (E.length + 1) s E []
  pure r.1

/-! ## Degrees -/

/-- **Degree after removing an edge.** Let $R$ be a finite list of edges of an undirected
multigraph, each an ordered pair of vertices, let $e = (a, b)$ be an edge in $R$, and let $x$ be a
vertex. Then the degree of $x$ in $R$ equals the degree of $x$ in the list obtained from $R$ by
removing the first occurrence of $e$, plus $[x = a] + [x = b]$, where $[P]$ is $1$ if $P$ holds
and $0$ otherwise. -/
theorem udeg_erase {R : List (V × V)} {e : V × V} (he : e ∈ R) (x : V) :
    udeg R x = udeg (R.erase e) x + (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0) := by
  have hp := List.perm_cons_erase he
  have h1 := (hp.map Prod.fst).count_eq x
  have h2 := (hp.map Prod.snd).count_eq x
  simp only [List.map_cons, List.count_cons, beq_iff_eq, @eq_comm _ e.1 x, @eq_comm _ e.2 x]
    at h1 h2
  unfold udeg
  rw [h1, h2]
  omega

theorem udeg_le_of_sublist {R R' : List (V × V)} (h : R'.Sublist R) (x : V) :
    udeg R' x ≤ udeg R x :=
  Nat.add_le_add ((h.map _).count_le x) ((h.map _).count_le x)

theorem udeg_pos_of_mem {R : List (V × V)} {e : V × V} (he : e ∈ R) :
    0 < udeg R e.1 ∧ 0 < udeg R e.2 := by
  have h1 : 0 < (R.map Prod.fst).count e.1 := List.count_pos_iff.2 (List.mem_map_of_mem he)
  have h2 : 0 < (R.map Prod.snd).count e.2 := List.count_pos_iff.2 (List.mem_map_of_mem he)
  unfold udeg; omega

/-- **An edge at a vertex joins it to its other endpoint.** If an ordered pair $e = (a, b)$ of
vertices has $a = v$ or $b = v$, then the unordered pair $\{a, b\}$ equals $\{v, w\}$, where $w$
is the other endpoint of $e$ at $v$. -/
theorem usym_eq_otherEnd {e : V × V} {v : V} (h : e.1 = v ∨ e.2 = v) :
    usym e = s(v, otherEnd e v) := by
  simp only [usym, otherEnd]
  split_ifs with h1
  · rw [h1]
  · rcases h with h | h
    · exact absurd h h1
    · rw [h, Sym2.eq_swap]

/-! ## The recursion -/

private theorem uvisit_none {fuel : ℕ} {v : V} {R : List (V × V)} (acc : List V)
    (h : R.find? (fun e => e.1 = v ∨ e.2 = v) = none) :
    uvisit (fuel + 1) v R acc = pure (v :: acc, R) := by
  rw [uvisit, h]

private theorem uvisit_some {fuel : ℕ} {v : V} {R : List (V × V)} {e : V × V} (acc : List V)
    (h : R.find? (fun e => e.1 = v ∨ e.2 = v) = some e) :
    (uvisit (fuel + 1) v R acc).ret =
        (uvisit fuel v (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.2
          (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.1).ret ∧
      (uvisit (fuel + 1) v R acc).time = 1 + (uvisit fuel (otherEnd e v) (R.erase e) acc).time +
        (uvisit fuel v (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.2
          (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.1).time := by
  rw [uvisit, h]
  constructor
  · simp
  · simp; omega

/-- **Invariant of the undirected Hierholzer recursion.** Let $R$ be a list of edges, $v$, $t$
vertices such that exactly $v$ and $t$ have odd degree in $R$ (no vertex when $v = t$), $A$ a list
of vertices, and $f > |R|$ a fuel bound. Run the undirected Hierholzer recursion with fuel $f$
from $v$ on $R$ with accumulator $A$, and let $R'$ be the remaining edge list it returns and $c$
its cost. Then there is a vertex sequence $W$ starting at $v$ and ending at $t$ such that the
returned vertex list is $W$ followed by $A$; the edges of $R$, as unordered pairs, are a
permutation of the consecutive pairs of $W$ followed by the edges of $R'$, all as unordered pairs;
every vertex has even degree in $R'$; every vertex of $W$ has degree $0$ in $R'$; $R'$ is a
sublist of $R$; and $c + |R'| = |R|$. -/
theorem uvisit_spec : ∀ (fuel : ℕ) (v t : V) (R : List (V × V)) (acc : List V),
    R.length < fuel → EvenExcept R v t →
    ∃ W, (uvisit fuel v R acc).ret.1 = W ++ acc ∧ W.head? = some v ∧ W.getLast? = some t ∧
      (R.map usym).Perm ((walkEdges W).map usym ++ (uvisit fuel v R acc).ret.2.map usym) ∧
      (∀ x, udeg (uvisit fuel v R acc).ret.2 x % 2 = 0) ∧
      (∀ x ∈ W, udeg (uvisit fuel v R acc).ret.2 x = 0) ∧
      (uvisit fuel v R acc).ret.2.Sublist R ∧
      (uvisit fuel v R acc).time + (uvisit fuel v R acc).ret.2.length = R.length
  | 0, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, v, t, R, acc, hlen, hpar => by
      cases hf : R.find? (fun e => e.1 = v ∨ e.2 = v) with
      | none =>
          -- no edge at `v`, so `v = t`
          have hdeg : udeg R v = 0 := by
            have hno : ∀ e ∈ R, ¬ (e.1 = v ∨ e.2 = v) := fun e he h => by
              simpa [h] using List.find?_eq_none.1 hf e he
            unfold udeg
            rw [Nat.add_eq_zero_iff, List.count_eq_zero, List.count_eq_zero]
            constructor
            · intro hm; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm; exact hno e he (Or.inl rfl)
            · intro hm; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm; exact hno e he (Or.inr rfl)
          have hvt : v = t := by
            have := hpar v
            rw [hdeg] at this
            by_contra hne
            simp [hne] at this
          subst hvt
          rw [uvisit_none acc hf]
          refine ⟨[v], rfl, rfl, rfl, by simp [walkEdges], fun x => ?_, ?_, List.Sublist.refl _,
            by simp⟩
          · have := hpar x
            simp only [TimeM.ret_pure]
            split_ifs at this <;> omega
          · intro x hx
            rw [List.mem_singleton] at hx
            subst hx
            simpa using hdeg
      | some e =>
          have he : e ∈ R := List.mem_of_find?_eq_some hf
          have hev : e.1 = v ∨ e.2 = v := by simpa using List.find?_some hf
          set w := otherEnd e v with hw
          -- the edge `e` joins `v` and `w`
          have hsym : usym e = s(v, w) := usym_eq_otherEnd hev
          have hind : ∀ x, (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0) =
              (if x = v then 1 else 0) + (if x = w then 1 else 0) := by
            intro x
            rcases hev with h | h
            · have hw' : w = e.2 := by simp [hw, otherEnd, h]
              rw [hw', h]
            · by_cases h1 : e.1 = v
              · have hw' : w = e.2 := by simp [hw, otherEnd, h1]
                rw [hw', h1]
              · have hw' : w = e.1 := by simp [hw, otherEnd, h1]
                rw [hw', h]; omega
          set R₁ := R.erase e with hR₁
          have hlenR₁ : R₁.length = R.length - 1 := by rw [hR₁]; exact List.length_erase_of_mem he
          have hRpos := List.length_pos_of_mem he
          have hlen₁ : R₁.length < fuel := by omega
          have hpar₁ : EvenExcept R₁ w t := by
            intro x
            have h1 := hpar x
            have h2 := udeg_erase he x
            have h3 := hind x
            rw [← hR₁] at h2
            split_ifs at h1 h2 h3 ⊢ <;> omega
          obtain ⟨W₁, hW₁, hW₁h, hW₁l, hp₁, hpar₂, hstuck₁, hsub₁, htime₁⟩ :=
            uvisit_spec fuel w t R₁ acc hlen₁ hpar₁
          set r₁ := (uvisit fuel w R₁ acc).ret with hr₁
          have hlen₂ : r₁.2.length < fuel := lt_of_le_of_lt hsub₁.length_le hlen₁
          have hpar₂' : EvenExcept r₁.2 v v := by
            intro x
            have := hpar₂ x
            split_ifs <;> omega
          obtain ⟨W₂, hW₂, hW₂h, hW₂l, hp₂, hpar₃, hstuck₂, hsub₂, htime₂⟩ :=
            uvisit_spec fuel v v r₁.2 r₁.1 hlen₂ hpar₂'
          obtain ⟨hret, htime⟩ := uvisit_some (fuel := fuel) acc hf
          rw [← hw, ← hR₁, ← hr₁] at hret htime
          refine ⟨W₂ ++ W₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hret, hW₂, hW₁, List.append_assoc]
          · cases W₂ with
            | nil => simp at hW₂h
            | cons y W₂ => simpa using hW₂h
          · rw [List.getLast?_append_of_ne_nil _ (by rintro rfl; simp at hW₁h)]; exact hW₁l
          · rw [hret, walkEdges_append hW₂l hW₁h]
            have hp₀ : (R.map usym).Perm (usym e :: R₁.map usym) := by
              have := (List.perm_cons_erase he).map usym
              simpa [hR₁] using this
            refine hp₀.trans ?_
            rw [hsym]
            have := (((hp₁.trans (hp₂.append_left _)).cons s(v, w)).trans
              (perm_splice s(v, w) ((walkEdges W₁).map usym) ((walkEdges W₂).map usym)
                ((uvisit fuel v r₁.2 r₁.1).ret.2.map usym)))
            simpa [List.map_append, List.map_cons, usym] using this
          · rw [hret]; exact hpar₃
          · intro x hx
            rw [hret]
            rcases List.mem_append.1 hx with hx | hx
            · exact hstuck₂ x hx
            · have := udeg_le_of_sublist hsub₂ x
              rw [hstuck₁ x hx] at this
              omega
          · rw [hret]
            exact hsub₂.trans (hsub₁.trans (List.erase_sublist))
          · rw [hret, htime]
            omega

/-! ## Correctness -/

omit [DecidableEq V] in
theorem mem_of_mem_walkEdges {W : List V} {a b : V} (h : (a, b) ∈ walkEdges W) :
    a ∈ W ∧ b ∈ W :=
  ⟨List.of_mem_zip h |>.1, List.mem_of_mem_tail (List.of_mem_zip h).2⟩

private theorem uhierholzer_facts (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t) :
    ∃ R' : List (V × V), (uhierholzer E s).ret.head? = some s ∧
      (uhierholzer E s).ret.getLast? = some t ∧
      (E.map usym).Perm ((walkEdges (uhierholzer E s).ret).map usym ++ R'.map usym) ∧
      (∀ x ∈ (uhierholzer E s).ret, udeg R' x = 0) ∧ R'.Sublist E ∧
      (uhierholzer E s).time + R'.length = E.length := by
  obtain ⟨W, hW, hh, hl, hp, -, hstuck, hsub, htime⟩ :=
    uvisit_spec (E.length + 1) s t E [] (Nat.lt_succ_self _) hpar
  rw [List.append_nil] at hW
  have hret : (uhierholzer E s).ret = W := by simp [uhierholzer, hW]
  have htime' : (uhierholzer E s).time = (uvisit (E.length + 1) s E []).time := by
    simp [uhierholzer]
  exact ⟨_, by rw [hret]; exact hh, by rw [hret]; exact hl, by rw [hret]; exact hp,
    by rw [hret]; exact hstuck, hsub, by rw [htime']; exact htime⟩

/-- **Undirected Hierholzer's algorithm returns a trail.** Let $E$ be a list of undirected edges
and $s$, $t$ vertices such that exactly $s$ and $t$ have odd degree in $E$ (no vertex has odd
degree when $s = t$). Then the vertex sequence $W$ returned by the undirected Hierholzer algorithm
on $E$ from $s$ starts at $s$ and ends at $t$, and the consecutive pairs of $W$, as unordered
pairs, form a sub-multiset of the edges of $E$ as unordered pairs: no edge is traversed more often
than it occurs in $E$. -/
theorem uhierholzer_trail (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t) :
    (uhierholzer E s).ret.head? = some s ∧ (uhierholzer E s).ret.getLast? = some t ∧
      ∃ rest, (E.map usym).Perm ((walkEdges (uhierholzer E s).ret).map usym ++ rest) := by
  obtain ⟨R', hh, hl, hp, -⟩ := uhierholzer_facts E s t hpar
  exact ⟨hh, hl, _, hp⟩

/-- A walk from `s` that removes its steps from `E` and leaves no edge at its own vertices
contains every vertex reachable from `s`. -/
private theorem mem_of_uReach {E R' : List (V × V)} {W : List V} {s : V}
    (hh : W.head? = some s)
    (hp : (E.map usym).Perm ((walkEdges W).map usym ++ R'.map usym))
    (hstuck : ∀ x ∈ W, udeg R' x = 0) : ∀ x, UReach E s x → x ∈ W := by
  intro x hx
  induction hx with
  | refl => exact List.mem_of_mem_head? hh
  | @tail a b _ hab ih =>
      have hmem : s(a, b) ∈ E.map usym := by
        rcases hab with h | h
        · exact List.mem_map.2 ⟨(a, b), h, rfl⟩
        · exact List.mem_map.2 ⟨(b, a), h, Sym2.eq_swap⟩
      rcases List.mem_append.1 (hp.subset hmem) with h | h
      · obtain ⟨⟨p, q⟩, hpq, he⟩ := List.mem_map.1 h
        have hpW := mem_of_mem_walkEdges hpq
        simp only [usym, Sym2.eq_iff] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hpW.2
        · exact hpW.1
      · obtain ⟨⟨p, q⟩, hpq, he⟩ := List.mem_map.1 h
        exfalso
        have h0 := hstuck a ih
        have hpos := udeg_pos_of_mem hpq
        simp only [usym, Sym2.eq_iff] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only at hpos; omega
        · simp only at hpos; omega

/-- **Undirected Hierholzer's algorithm finds Euler paths.** Let $E$ be a list of undirected edges
(ordered pairs of vertices) and $s$, $t$ vertices such that exactly $s$ and $t$ have odd degree in
$E$ (no vertex has odd degree when $s = t$), and suppose the first endpoint of every edge of $E$ is
reachable from $s$ through edges of $E$. Then the vertex sequence returned by the undirected
Hierholzer algorithm on $E$ from $s$ is an Euler path of $E$ from $s$ to $t$. -/
theorem uhierholzer_isUEulerPath (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t)
    (hreach : ∀ e ∈ E, UReach E s e.1) : IsUEulerPath E s t (uhierholzer E s).ret := by
  obtain ⟨R', hh, hl, hp, hstuck, hsub, -⟩ := uhierholzer_facts E s t hpar
  have hR' : R' = [] := by
    rcases R' with _ | ⟨e', R''⟩
    · rfl
    · exfalso
      have he' : e' ∈ E := hsub.subset List.mem_cons_self
      have h0 := hstuck e'.1 (mem_of_uReach hh hp hstuck e'.1 (hreach e' he'))
      have := (udeg_pos_of_mem (List.mem_cons_self (a := e') (l := R''))).1
      omega
  subst hR'
  refine ⟨hh, hl, ?_⟩
  simpa using hp.symm

/-- **Undirected Hierholzer's algorithm finds Euler circuits.** Let $E$ be a list of undirected
edges (ordered pairs of vertices) in which every vertex has even degree, and let $s$ be a vertex
such that the first endpoint of every edge of $E$ is reachable from $s$ through edges of $E$. Then
the vertex sequence returned by the undirected Hierholzer algorithm on $E$ from $s$ is an Euler
path of $E$ from $s$ to $s$, that is, an Euler circuit at $s$. -/
theorem uhierholzer_isUEulerCircuit (E : List (V × V)) (s : V) (hpar : ∀ x, udeg E x % 2 = 0)
    (hreach : ∀ e ∈ E, UReach E s e.1) : IsUEulerPath E s s (uhierholzer E s).ret :=
  uhierholzer_isUEulerPath E s s (fun x => by have := hpar x; split_ifs <;> omega) hreach

/-- **Cost of the undirected Hierholzer algorithm.** Let $E$ be a list of undirected edges and
$s$, $t$ vertices such that exactly $s$ and $t$ have odd degree in $E$ (no vertex has odd degree
when $s = t$), and suppose the first endpoint of every edge of $E$ is reachable from $s$ through
edges of $E$. Then the undirected Hierholzer algorithm on $E$ from $s$ costs exactly $|E|$, the
number of edges of $E$, in the cost model that charges one unit per removed edge. -/
theorem uhierholzer_time (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t)
    (hreach : ∀ e ∈ E, UReach E s e.1) : (uhierholzer E s).time = E.length := by
  obtain ⟨R', hh, hl, hp, hstuck, hsub, htime⟩ := uhierholzer_facts E s t hpar
  have hR' : R' = [] := by
    rcases R' with _ | ⟨e', R''⟩
    · rfl
    · exfalso
      have he' : e' ∈ E := hsub.subset List.mem_cons_self
      have h0 := hstuck e'.1 (mem_of_uReach hh hp hstuck e'.1 (hreach e' he'))
      have := (udeg_pos_of_mem (List.mem_cons_self (a := e') (l := R''))).1
      omega
  subst hR'
  simpa using htime

/-! ## The converse: degrees of an Euler path -/

/-- **Multiplicity of a vertex in an unordered edge.** For a vertex $x$, this assigns to an
unordered pair $\{a, b\}$ the number $[x = a] + [x = b]$ of its endpoints equal to $x$, where
$[P]$ is $1$ if $P$ holds and $0$ otherwise; in particular a loop $\{x, x\}$ gives $2$. -/
def endsAt (x : V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => (if x = a then 1 else 0) + (if x = b then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩

theorem endsAt_usym (x : V) (e : V × V) :
    endsAt x (usym e) = (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0) := rfl

theorem udeg_eq_sum (R : List (V × V)) (x : V) :
    udeg R x = ((R.map usym).map (endsAt x)).sum := by
  induction R with
  | nil => simp [udeg]
  | cons e R ih =>
      simp only [udeg] at ih ⊢
      simp only [List.map_cons, List.count_cons, beq_iff_eq, List.sum_cons, endsAt_usym,
        @eq_comm _ e.1 x, @eq_comm _ e.2 x]
      omega

/-- **Degrees depend only on the unordered edges.** Let $A$ and $B$ be finite lists of edges of an
undirected multigraph such that the multiset of edges of $A$, taken as unordered pairs, equals that
of $B$. Then every vertex has the same degree in $A$ as in $B$. -/
theorem udeg_eq_of_perm {A B : List (V × V)} (h : (A.map usym).Perm (B.map usym)) (x : V) :
    udeg A x = udeg B x := by
  rw [udeg_eq_sum, udeg_eq_sum]
  exact (h.map _).sum_eq

/-- **Degrees along a walk.** Let $W = (w_0, \dots, w_n)$ be a nonempty sequence of vertices with
$w_0 = s$ and $w_n = t$, and consider the multigraph whose edges are the consecutive pairs
$(w_{i-1}, w_i)$ for $1 \le i \le n$. In it every vertex other than $s$ and $t$ has even degree
(a loop counts twice); if $s \ne t$, then $s$ and $t$ have odd degree, and if $s = t$, every
vertex has even degree. -/
theorem evenExcept_walkEdges : ∀ (W : List V) (s t : V), W.head? = some s →
    W.getLast? = some t → EvenExcept (walkEdges W) s t
  | [], _, _, h, _, _ => by simp at h
  | [a], s, t, hs, ht, x => by
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hs ht
      subst hs ht
      simp only [walkEdges, List.tail_cons, List.zip_nil_right, udeg, List.map_nil,
        List.count_nil]
      split_ifs <;> omega
  | a :: b :: W, s, t, hs, ht, x => by
      simp only [List.head?_cons, Option.some.injEq] at hs
      subst hs
      rw [List.getLast?_cons_cons] at ht
      have ih := evenExcept_walkEdges (b :: W) b t rfl ht x
      have e : walkEdges (a :: b :: W) = (a, b) :: walkEdges (b :: W) := rfl
      rw [e]
      simp only [udeg, List.map_cons, List.count_cons, beq_iff_eq, @eq_comm _ a x,
        @eq_comm _ b x] at ih ⊢
      split_ifs at ih ⊢ <;> omega

/-- **Degrees of an undirected Euler path.** Let $E$ be a finite list of edges of an undirected
multigraph and let $W$ be an Euler path of $E$ from $s$ to $t$. Then every vertex other than $s$
and $t$ has even degree in $E$ (a loop counts twice); if $s \ne t$, then $s$ and $t$ have odd
degree, and if $s = t$, every vertex has even degree. -/
theorem evenExcept_of_isUEulerPath {E : List (V × V)} {s t : V} {W : List V}
    (h : IsUEulerPath E s t W) : EvenExcept E s t := by
  intro x
  rw [← udeg_eq_of_perm h.2.2 x]
  exact evenExcept_walkEdges W s t h.1 h.2.1 x

/-- **Euler's theorem for undirected multigraphs.** Let $E$ be a finite list of edges of an
undirected multigraph (parallel edges and loops allowed), each given as a pair $(a, b)$, and let
$s$, $t$ be vertices such that the first endpoint $a$ of every edge is reachable from $s$ along
edges of $E$ traversed in either direction. Then $E$ has an Euler path from $s$ to $t$ if and only
if, when $s \ne t$, exactly $s$ and $t$ have odd degree, and, when $s = t$, every vertex has even
degree (a loop counts twice towards the degree).

This is the algorithmic form: the proof shows that Hierholzer's algorithm started at $s$ finds
such a path. -/
theorem exists_isUEulerPath_iff (E : List (V × V)) (s t : V)
    (hreach : ∀ e ∈ E, UReach E s e.1) :
    (∃ W, IsUEulerPath E s t W) ↔ EvenExcept E s t :=
  ⟨fun ⟨_, h⟩ => evenExcept_of_isUEulerPath h,
    fun h => ⟨_, uhierholzer_isUEulerPath E s t h hreach⟩⟩

end Cslib.Algorithms.Lean.Hierholzer
