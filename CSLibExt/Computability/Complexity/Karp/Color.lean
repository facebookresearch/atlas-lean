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

/-- A graph: `n` in unary, then each edge `(u, v)` as `u` and `v` in unary. -/
def encodeE (n : ℕ) (es : List (ℕ × ℕ)) : List Bool :=
  List.replicate n true ++ false ::
    es.flatMap fun e => List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false])

/-- The graph on `Fin n` with edge list `es` (symmetrized, loops dropped). -/
def edgeGraph (n : ℕ) (es : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ((i : ℕ), (j : ℕ)) ∈ es

open Classical in
/-- 3-COLOR: encodings of 3-colorable graphs. -/
noncomputable def col3Dec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ n es, encodeE n es = x ∧ (∀ e ∈ es, e.1 < n ∧ e.2 < n) ∧
    (edgeGraph n es).Colorable 3)

/-- State of the construction: the next free vertex, the earlier occurrences (variable,
polarity, literal vertex, negation vertex; latest first), and the edges emitted so far. -/
structure ColSt where
  /-- The next free vertex. -/
  next : ℕ
  /-- Earlier occurrences, latest first. -/
  prev : List (ℕ × Bool × ℕ × ℕ)
  /-- Emitted edges, in emission order. -/
  em : List (ℕ × ℕ)
deriving DecidableEq

/-- Consistency edges of a new occurrence (`L`, `M`) of literal `l` with an earlier one. -/
def consEdges (l : ℕ × Bool) (L M : ℕ) (q : ℕ × Bool × ℕ × ℕ) : List (ℕ × ℕ) :=
  if q.1 = l.1 then
    if q.2.1 = l.2 then [(q.2.2.1, M), (q.2.2.2, L)] else [(q.2.2.1, L), (q.2.2.2, M)]
  else []

/-- A new occurrence of literal `l`: its two vertices, their triangle with `B`, consistency edges
with the earlier occurrences (latest first). Returns the literal vertex. -/
def colOcc (l : ℕ × Bool) (s : ColSt) : ColSt × ℕ :=
  let L := s.next
  let M := s.next + 1
  ({ next := s.next + 2, prev := (l.1, l.2, L, M) :: s.prev,
     em := s.em ++ [(L, M), (L, 2), (M, 2)] ++ s.prev.flatMap (consEdges l L M) }, L)

/-- An OR gadget with inputs `a` and `o`; returns its output vertex. -/
def colOr (a o : ℕ) (s : ColSt) : ColSt × ℕ :=
  let u := s.next
  let v := s.next + 1
  let w := s.next + 2
  ({ s with next := s.next + 3, em := s.em ++ [(a, u), (o, v), (u, v), (u, w), (v, w), (w, 2)] },
    w)

/-- The remaining literals of a clause (walk order), `o` being the output so far; at the end the
output is joined to `F` and `B`. -/
def colLits : List (ℕ × Bool) → ℕ → ColSt → ColSt
  | [], o, s => { s with em := s.em ++ [(o, 1), (o, 2)] }
  | l :: ls, o, s =>
      let r := colOcc l s
      let r' := colOr r.2 o r.1
      colLits ls r'.2 r'.1

/-- One clause; its literals are walked from the last one. -/
def colClause (C : CNFClause) (s : ColSt) : ColSt :=
  match C.reverse with
  | [] => { s with next := s.next + 1, em := s.em ++ [(s.next, 0), (s.next, 1), (s.next, 2)] }
  | l :: ls =>
      let r := colOcc l s
      colLits ls r.2 r.1

/-- The whole construction: palette triangle first, then the clauses from the last one. -/
def colSt (φ : CNF) : ColSt :=
  φ.reverse.foldl (fun s C => colClause C s) ⟨3, [], [(0, 1), (0, 2), (1, 2)]⟩

/-- The 3-COLOR instance of a formula. -/
def toCol (φ : CNF) : List Bool := encodeE (colSt φ).next (colSt φ).em.reverse

/-- A fixed no-instance: the complete graph on four vertices. -/
def noCol : List Bool := encodeE 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- SAT ≤ 3-COLOR on bit strings. -/
def reduceCol (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => toCol φ
  | none => noCol

/-! ### Parsing an edge list

`decodeE` inverts `encodeE` (`decodeE_encodeE`, `encodeE_of_decodeE`); shared by the 3-COLOR
verifier and the PATH decider. -/

/-- A unary read strictly shortens the input. -/
theorem length_lt_of_readUnaryLength {x r : List Bool} {u : ℕ}
    (h : readUnaryLength x = some (u, r)) : r.length < x.length := by
  rw [(readUnaryLength_eq_some_iff x u r).1 h]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The edge list after `n`: pairs of unary numbers until the input ends; `none` on a dangling
half-pair or a cut-off number. -/
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

/-- Parse a graph: `n` in unary, then the edge list. -/
def decodeE (x : List Bool) : Option (ℕ × List (ℕ × ℕ)) :=
  match readUnaryLength x with
  | none => none
  | some (n, r) => (decodeEs r).map ((n, ·))

/-- The bits of an edge list. -/
def edgeBits (es : List (ℕ × ℕ)) : List Bool :=
  es.flatMap fun e => List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false])

/-- The empty edge list. -/
theorem decodeEs_nil : decodeEs [] = some [] := by
  rw [decodeEs]; simp

/-- A nonempty input whose first number is cut off. -/
theorem decodeEs_of_none {x : List Bool} (hx : x ≠ []) (h : readUnaryLength x = none) :
    decodeEs x = none := by
  rw [decodeEs]
  simp only [hx, ite_false]
  split <;> simp_all

/-- A dangling half-pair. -/
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

/-- A full pair, then the rest. -/
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

/-- `decodeEs` reads back an edge list. -/
theorem decodeEs_edgeBits : ∀ es, decodeEs (edgeBits es) = some es
  | [] => decodeEs_nil
  | (u, v) :: es => by
      have e : edgeBits ((u, v) :: es) =
          List.replicate u true ++ false :: (List.replicate v true ++ false :: edgeBits es) := by
        simp [edgeBits]
      rw [e, decodeEs_of_some_some (readUnaryLength_replicate _ _) (readUnaryLength_replicate _ _),
        decodeEs_edgeBits es]
      rfl

/-- `decodeEs` succeeds only on edge lists. -/
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

/-- `encodeE` is `n` in unary, then the edge bits. -/
theorem encodeE_eq (n : ℕ) (es : List (ℕ × ℕ)) :
    encodeE n es = List.replicate n true ++ false :: edgeBits es := rfl

/-- `decodeE` inverts `encodeE`. -/
theorem decodeE_encodeE (n : ℕ) (es : List (ℕ × ℕ)) : decodeE (encodeE n es) = some (n, es) := by
  simp [decodeE, encodeE_eq, decodeEs_edgeBits]

/-- `decodeE` succeeds only on encodings. -/
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
