/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Karp reductions on the canonical classes: 3-COLOR

Specification module for SAT ≤ 3-COLOR on `MetaMathlibExt.ComplexityTheory` (Karp 1972, via the
OR-gadget construction of Garey–Johnson–Stockmeyer). It fixes the instance encoding, the language
(through Mathlib's `SimpleGraph.Colorable`) and the pure reduction; the correctness proof, the
machines and NP membership are separate components.

* Graphs: `encodeE n es` is `n` in unary, then every edge `(u, v)` as `u` and `v` in unary.
  `edgeGraph n es : SimpleGraph (Fin n)` is the graph (`SimpleGraph.fromRel`, so loops are
  dropped and edges are symmetric).
* `col3Dec`: encodings of 3-colorable graphs whose edges have endpoints below `n`.
* `toCol φ`, built by `colSt`: vertices `0, 1, 2` are the palette `T, F, B` (a triangle). The
  clauses are walked from the last one and, in each, the literals from the last one, the order in
  which a machine meets them on the SAT token stack. Each literal occurrence gets two fresh
  vertices `L, M` (`colOcc`: triangle `L, M, B`; consistency edges to every earlier occurrence of
  the same variable, `(L', M), (M', L)` for equal polarity and `(L', L), (M', M)` otherwise).
  Within a clause the occurrences are or-ed by OR gadgets (`colOr`: three fresh vertices
  `u, v, w`, edges `(a, u), (o, v), (u, v), (u, w), (v, w), (w, B)`), and the clause's output is
  joined to `F` and `B` (`colLits`); an empty clause gets a vertex joined to all three palette
  vertices. Edges are emitted in that order; the instance lists them in reverse (`em.reverse`),
  the order in which a machine pushing them meets them. `reduceCol` is the reduction on bit
  strings; undecodable input goes to `noCol` (the complete graph on four vertices).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-- **Bit-string encoding of a graph.** The graph encoding of a number $n$ and a list $E$ of pairs
of natural numbers is the bit string that writes $n$ in unary and then, for each pair $(u, v)$
of $E$ in order, writes $u$ and then $v$ in unary, where a natural number $k$ is written in
unary as $k$ ones followed by one zero. -/
def encodeE (n : ℕ) (es : List (ℕ × ℕ)) : List Bool :=
  List.replicate n true ++ false ::
    es.flatMap fun e => List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false])

/-- **Graph of an edge list.** For a natural number $n$ and a list $es$ of pairs of natural
numbers, the graph of $es$ on $n$ vertices is the simple graph on $\{0, \dots, n-1\}$ in which
distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $es$. Loops are
dropped, and pairs with an endpoint at least $n$ contribute no edge. -/
def edgeGraph (n : ℕ) (es : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ((i : ℕ), (j : ℕ)) ∈ es

open Classical in
/-- **3-COLOR.** The decision problem 3-COLOR accepts a bit string $x$ exactly when there are a
natural number $n$ and a list $es$ of pairs of natural numbers such that $x$ is the encoding of
$n$ and $es$ ($n$ in unary, then each edge $(u, v)$ as $u$ and $v$ in unary), every edge
$(u, v)$ in $es$ has $u < n$ and $v < n$, and the graph on $\{0, \dots, n - 1\}$ with edge list
$es$ (symmetrized, loops dropped) is $3$-colorable. -/
noncomputable def col3Dec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ n es, encodeE n es = x ∧ (∀ e ∈ es, e.1 < n ∧ e.2 < n) ∧
    (edgeGraph n es).Colorable 3)

/-- **State of the SAT-to-3-COLOR construction.** A state of the graph construction reducing CNF
satisfiability to 3-colorability consists of a natural number, the next free vertex; a list of
quadruples $(x, b, L, M)$ of a variable index $x$, a polarity $b$, the vertex $L$ of the literal
and the vertex $M$ of its negation, recording the earlier literal occurrences with the latest
first; and a list of pairs of natural numbers, the edges emitted so far, in emission order. -/
structure ColSt where
  /-- The next free vertex. -/
  next : ℕ
  /-- Earlier occurrences, latest first. -/
  prev : List (ℕ × Bool × ℕ × ℕ)
  /-- Emitted edges, in emission order. -/
  em : List (ℕ × ℕ)
deriving DecidableEq

/-- **Consistency edges between two occurrences of a variable.** Let $l = (x, b)$ be a literal
with variable index $x$ and polarity $b$, let $L$, $M$ be the vertices of a new occurrence of
$l$, and let $(x', b', L', M')$ be an earlier occurrence. If $x' \ne x$ the list of consistency
edges is empty. If $x' = x$ and $b' = b$ it is $[(L', M), (M', L)]$; if $x' = x$ and $b' \ne b$
it is $[(L', L), (M', M)]$. -/
def consEdges (l : ℕ × Bool) (L M : ℕ) (q : ℕ × Bool × ℕ × ℕ) : List (ℕ × ℕ) :=
  if q.1 = l.1 then
    if q.2.1 = l.2 then [(q.2.2.1, M), (q.2.2.2, L)] else [(q.2.2.1, L), (q.2.2.2, M)]
  else []

/-- **Adding a literal occurrence in the 3-COLOR construction.** Given a literal $l = (x, b)$
with variable index $x$ and polarity $b$, and a state whose next free vertex is $n$, let $L = n$
and $M = n + 1$. The new state has next free vertex $n + 2$, records the occurrence
$(x, b, L, M)$ at the front of the list of earlier occurrences, and appends to the emitted edges
first $(L, M)$, $(L, 2)$, $(M, 2)$ (a triangle with the palette vertex $2$), then the
consistency edges of the new occurrence $(L, M)$ of $l$ with each earlier occurrence, taken
latest first. The result is this new state together with the vertex $L$. -/
def colOcc (l : ℕ × Bool) (s : ColSt) : ColSt × ℕ :=
  let L := s.next
  let M := s.next + 1
  ({ next := s.next + 2, prev := (l.1, l.2, L, M) :: s.prev,
     em := s.em ++ [(L, M), (L, 2), (M, 2)] ++ s.prev.flatMap (consEdges l L M) }, L)

/-- **OR gadget of the 3-COLOR construction.** Given vertices $a$ and $o$ and a state whose next
free vertex is $n$, let $u = n$, $v = n + 1$ and $w = n + 2$. The new state has next free vertex
$n + 3$, the same earlier occurrences, and the emitted edges followed by $(a, u)$, $(o, v)$,
$(u, v)$, $(u, w)$, $(v, w)$, $(w, 2)$. The result is this new state together with the output
vertex $w$. -/
def colOr (a o : ℕ) (s : ColSt) : ColSt × ℕ :=
  let u := s.next
  let v := s.next + 1
  let w := s.next + 2
  ({ s with next := s.next + 3, em := s.em ++ [(a, u), (o, v), (u, v), (u, w), (v, w), (w, 2)] },
    w)

/-- **Processing the remaining literals of a clause.** Given a list of literals, a vertex $o$
(the output so far) and a state, the result is defined by recursion on the list. For the empty
list, the emitted edges of the state are followed by $(o, 1)$ and $(o, 2)$, joining $o$ to the
palette vertices $1$ and $2$, and the other components are unchanged. For a list with head $l$
and tail $ls$, first add an occurrence of $l$, obtaining a state and the literal vertex $L$;
then add an OR gadget with inputs $L$ and $o$, obtaining a state and its output vertex $w$;
then process $ls$ with output $w$ from that state. -/
def colLits : List (ℕ × Bool) → ℕ → ColSt → ColSt
  | [], o, s => { s with em := s.em ++ [(o, 1), (o, 2)] }
  | l :: ls, o, s =>
      let r := colOcc l s
      let r' := colOr r.2 o r.1
      colLits ls r'.2 r'.1

/-- **Processing one clause in the 3-COLOR construction.** Given a clause $C$ and a state
whose next free vertex is $n$, the literals of $C$ are read from the last one. If $C$ is empty,
the new state has next free vertex $n + 1$, the same earlier occurrences, and the emitted edges
followed by $(n, 0)$, $(n, 1)$, $(n, 2)$, joining the fresh vertex $n$ to the palette vertices
$0$, $1$, $2$. Otherwise let $l$ be the last literal of $C$ and $ls$ the other literals in
reverse order: add an occurrence of $l$, obtaining a state and the literal vertex $L$, then
process the remaining literals $ls$ with output $L$ from that state. -/
def colClause (C : CNFClause) (s : ColSt) : ColSt :=
  match C.reverse with
  | [] => { s with next := s.next + 1, em := s.em ++ [(s.next, 0), (s.next, 1), (s.next, 2)] }
  | l :: ls =>
      let r := colOcc l s
      colLits ls r.2 r.1

/-- **The SAT-to-3-COLOR graph construction.** For a CNF formula $\varphi$, start from the state
whose next free vertex is $3$, with no earlier occurrences and with emitted edges $(0, 1)$,
$(0, 2)$, $(1, 2)$ (the palette triangle on the vertices $0$, $1$, $2$), and process the
clauses of $\varphi$ one at a time, from the last clause to the first. The result is the final
state. -/
def colSt (φ : CNF) : ColSt :=
  φ.reverse.foldl (fun s C => colClause C s) ⟨3, [], [(0, 1), (0, 2), (1, 2)]⟩

/-- **The 3-COLOR instance of a CNF formula.** Run the gadget construction on a CNF formula
$\varphi$; it ends with a next free vertex $N$ and a list of emitted edges. The 3-COLOR instance
of $\varphi$ is the graph encoding of the number $N$ and the emitted edges in reverse order. -/
def toCol (φ : CNF) : List Bool := encodeE (colSt φ).next (colSt φ).em.reverse

/-- **The complete graph on four vertices as a bit string.** This is the graph encoding of the
number $4$ and the edge list $(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)$, in that order,
that is, of the complete graph on the vertices $0, 1, 2, 3$.

This graph is not 3-colorable; the reduction from SAT to 3-COLOR sends undecodable input to it. -/
def noCol : List Bool := encodeE 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- **The SAT to 3-COLOR reduction map on bit strings.** The map sends a bit string $x$ that
decodes to a CNF formula $\varphi$ to the 3-COLOR instance of $\varphi$, and sends every bit
string that does not decode to a CNF formula to the graph encoding of the number $4$ and the
edge list $(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)$, in that order, that is, of the
complete graph on four vertices. -/
def reduceCol (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => toCol φ
  | none => noCol

/-! ### Parsing an edge list

`decodeE` inverts `encodeE` (`decodeE_encodeE`, `encodeE_of_decodeE`); shared by the 3-COLOR
verifier and the PATH decider. -/

/-- **Reading a unary number shortens the input.** If reading a unary length prefix from a bit
string $x$ succeeds with value $u$ and unconsumed suffix $r$, then $r$ is strictly shorter
than $x$. -/
theorem length_lt_of_readUnaryLength {x r : List Bool} {u : ℕ}
    (h : readUnaryLength x = some (u, r)) : r.length < x.length := by
  rw [(readUnaryLength_eq_some_iff x u r).1 h]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- **Edge-list decoder.** The edge-list decoder reads a bit string as a list of pairs of natural
numbers, each number written in unary as that many $1$s followed by a $0$. On the empty string
it returns the empty list. Otherwise it reads a number $u$, then a number $v$, decodes the rest
recursively, and returns $(u, v)$ followed by the result; it fails if the input ends inside a
number or after an unpaired number, or if decoding the rest fails.

In a graph encoding it parses what follows the vertex count. -/
def decodeEs (x : List Bool) : Option (List (ℕ × ℕ)) :=
  if x = [] then some [] else
    match h₁ : readUnaryLength x with
    | none => none
    | some (u, r) =>
        match h₂ : readUnaryLength r with
        | none => none
        | some (v, r') =>
            have : r'.length < x.length :=
              (length_lt_of_readUnaryLength h₂).trans (length_lt_of_readUnaryLength h₁)
            (decodeEs r').map ((u, v) :: ·)
termination_by x.length

/-- **Decoding a graph.** To decode a bit string $x$, read a unary number $n$ from the front of
$x$ ($n$ copies of true ended by false); if there is none, decoding fails. Otherwise decode the
rest of $x$ as an edge list $es$ (pairs of unary numbers until the input ends); if that fails,
decoding fails, and otherwise the result is the pair $(n, es)$. -/
def decodeE (x : List Bool) : Option (ℕ × List (ℕ × ℕ)) :=
  match readUnaryLength x with
  | none => none
  | some (n, r) => (decodeEs r).map ((n, ·))

/-- **Bit encoding of an edge list.** The edge bits of a list of pairs of natural numbers are the
concatenation, over its pairs $(u, v)$ in order, of $u$ ones, a zero, $v$ ones and a zero. -/
def edgeBits (es : List (ℕ × ℕ)) : List Bool :=
  es.flatMap fun e => List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false])

/-- **Decoding the empty input.** The edge-list decoder, applied to the empty bit string,
succeeds and returns the empty edge list. -/
theorem decodeEs_nil : decodeEs [] = some [] := by
  rw [decodeEs]; simp

/-- **The edge-list decoder fails on a cut-off first number.** If $x$ is a nonempty bit string
and reading a unary length prefix from $x$ fails, then the edge-list decoder fails on $x$. -/
theorem decodeEs_of_none {x : List Bool} (hx : x ≠ []) (h : readUnaryLength x = none) :
    decodeEs x = none := by
  rw [decodeEs]
  simp only [hx, ite_false]
  split <;> simp_all

/-- **Decoding fails on a dangling half-pair.** If reading a unary length prefix from a bit string
$x$ returns a number $u$ and the remaining suffix $r$, and reading a unary length prefix from $r$
fails, then the edge-list decoder fails on $x$. -/
theorem decodeEs_of_some_none {x r : List Bool} {u : ℕ} (h₁ : readUnaryLength x = some (u, r))
    (h₂ : readUnaryLength r = none) : decodeEs x = none := by
  have hx : x ≠ [] := by rintro rfl; simp [readUnaryLength] at h₁
  rw [decodeEs]
  simp only [hx, ite_false]
  split
  · rfl
  · rename_i u' r' h₁'
    rw [h₁] at h₁'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁')
    split <;> simp_all

/-- **Decoding one pair, then the rest.** If reading a unary length prefix from a bit string $x$
returns $u$ with remaining suffix $r$, and reading one from $r$ returns $v$ with remaining suffix
$r'$, then the edge-list decoder succeeds on $x$ exactly when it succeeds on $r'$, and in that
case its result on $x$ is its result on $r'$ with the pair $(u, v)$ put in front. -/
theorem decodeEs_of_some_some {x r r' : List Bool} {u v : ℕ}
    (h₁ : readUnaryLength x = some (u, r)) (h₂ : readUnaryLength r = some (v, r')) :
    decodeEs x = (decodeEs r').map ((u, v) :: ·) := by
  have hx : x ≠ [] := by rintro rfl; simp [readUnaryLength] at h₁
  rw [decodeEs]
  simp only [hx, ite_false]
  split
  · simp_all
  · rename_i u' r₁ h₁'
    rw [h₁] at h₁'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁')
    split
    · simp_all
    · rename_i v' r₂ h₂'
      rw [h₂] at h₂'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂')
      rfl

/-- **Decoding the bits of an edge list.** For every list $es$ of pairs of natural numbers, the
edge-list decoder applied to the edge bits of $es$ succeeds and returns $es$. -/
theorem decodeEs_edgeBits : ∀ es, decodeEs (edgeBits es) = some es
  | [] => decodeEs_nil
  | (u, v) :: es => by
      have e : edgeBits ((u, v) :: es) =
          List.replicate u true ++ false :: (List.replicate v true ++ false :: edgeBits es) := by
        simp [edgeBits]
      rw [e, decodeEs_of_some_some (readUnaryLength_replicate _ _) (readUnaryLength_replicate _ _),
        decodeEs_edgeBits es]
      rfl

/-- **The edge-list decoder succeeds only on edge bits.** For every bit string $x$ and every list
$es$ of pairs of natural numbers, if the edge-list decoder returns $es$ on $x$, then $x$ is the
edge bits of $es$. -/
theorem edgeBits_of_decodeEs : ∀ {es : List (ℕ × ℕ)} {x : List Bool},
    decodeEs x = some es → edgeBits es = x
  | [], x, h => by
      by_cases hx : x = []
      · rw [hx]; rfl
      · rw [decodeEs] at h
        simp only [hx, ite_false] at h
        split at h <;> (try split at h) <;> simp at h
  | (u, v) :: es, x, h => by
      have hx : x ≠ [] := by rintro rfl; simp [decodeEs_nil] at h
      cases h₁ : readUnaryLength x with
      | none => simp [decodeEs_of_none hx h₁] at h
      | some p =>
          obtain ⟨u', r⟩ := p
          cases h₂ : readUnaryLength r with
          | none => simp [decodeEs_of_some_none h₁ h₂] at h
          | some q =>
              obtain ⟨v', r'⟩ := q
              rw [decodeEs_of_some_some h₁ h₂] at h
              cases h₃ : decodeEs r' with
              | none => simp [h₃] at h
              | some es' =>
                  simp only [h₃, Option.map_some, Option.some.injEq, List.cons.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                  rw [(readUnaryLength_eq_some_iff _ _ _).1 h₁,
                    (readUnaryLength_eq_some_iff _ _ _).1 h₂, ← edgeBits_of_decodeEs h₃]
                  simp [edgeBits]

/-- **Graph encoding as vertex count plus edge bits.** For every natural number $n$ and every list
$es$ of pairs of natural numbers, the graph encoding of $n$ and $es$ is $n$ ones, then a zero,
then the edge bits of $es$. -/
theorem encodeE_eq (n : ℕ) (es : List (ℕ × ℕ)) :
    encodeE n es = List.replicate n true ++ false :: edgeBits es := rfl

/-- **Graph decoding inverts graph encoding.** For every natural number $n$ and every list $es$
of pairs of natural numbers, decoding the graph encoding of $n$ and $es$ succeeds and returns
$(n, es)$. -/
theorem decodeE_encodeE (n : ℕ) (es : List (ℕ × ℕ)) : decodeE (encodeE n es) = some (n, es) := by
  simp [decodeE, encodeE_eq, decodeEs_edgeBits]

/-- **Graph decoding succeeds only on encodings.** Let $x$ be a bit string. If decoding $x$ as a
graph yields a number $n$ and a list $E$ of pairs of natural numbers, then $x$ is the graph
encoding of $n$ and $E$. -/
theorem encodeE_of_decodeE {x : List Bool} {n : ℕ} {es : List (ℕ × ℕ)}
    (h : decodeE x = some (n, es)) : encodeE n es = x := by
  unfold decodeE at h
  split at h
  · simp at h
  · rename_i n' r hr
    cases h₂ : decodeEs r with
    | none => simp [h₂] at h
    | some es' =>
        simp only [h₂, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [(readUnaryLength_eq_some_iff _ _ _).1 hr, encodeE_eq, edgeBits_of_decodeEs h₂]

end Cslib.Complexity.Karp
