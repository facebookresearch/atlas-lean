/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPath
public import CSLibExt.Computability.Complexity.PathCorrect
public import Mathlib.Tactic.Linarith

/-!
# The NP verifier for HAMPATH: the check as a pure function

A witness lists the vertices of a path in unary, each followed by `false` (`encW`); `decodeW`
reads one back exactly (`decodeW_eq_some`). `hamCheck x w` accepts iff `x` decodes to a
PATH instance `(s, t, n, es)` (`Path.decodeP`), `w` decodes to a vertex list `p`, and `p`
passes `hamOk`, the decidable form of `IsHamPath n es s t p` (`hamOk_iff`).

* `hamPathDec_iff`: HAMPATH is verified by `hamCheck` with witnesses of at most `(|x| + 1)²`
  bits (a Hamiltonian path has `n ≤ |x|` vertices, each below `n`).
* The machine's view (`walkOk`, `stepOk`): it walks the vertices in order, checking each one is
  below `n`, the first one is `s` and each later one follows its predecessor along a listed
  edge, and no later vertex repeats it; at the end it checks the count `n` and the last vertex
  `t`, and that there was a vertex at all. `walkOk_eq`: this is `hamOk`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.HamVerify

open Cslib.CookLevin

/-- The bits of an edge list, first edge first. -/
theorem edgeBits_cons (u v : ℕ) (es : List (ℕ × ℕ)) : Karp.edgeBits ((u, v) :: es) =
    List.replicate u true ++ false :: (List.replicate v true ++ false :: Karp.edgeBits es) := by
  simp [Karp.edgeBits]

/-- No edges, no bits. -/
@[simp] theorem edgeBits_nil : Karp.edgeBits [] = [] := rfl

/-- The bits of a concatenation of edge lists. -/
theorem edgeBits_append (es es' : List (ℕ × ℕ)) :
    Karp.edgeBits (es ++ es') = Karp.edgeBits es ++ Karp.edgeBits es' :=
  List.flatMap_append

/-! ### Witnesses -/

/-- A witness: the vertices of a path in unary, each followed by `false`. -/
def encW (p : List ℕ) : List Bool := p.flatMap fun v => List.replicate v true ++ [false]

/-- Parse a witness: unary numbers until the input ends; `none` on a cut-off number. -/
def decodeW (w : List Bool) : Option (List ℕ) :=
  if w = [] then some [] else
    match h : readUnaryLength w with
    | none => none
    | some (v, r) =>
        have : r.length < w.length := Karp.length_lt_of_readUnaryLength h
        (decodeW r).map (v :: ·)
termination_by w.length

/-- The empty witness. -/
@[simp] theorem encW_nil : encW [] = [] := rfl

/-- The first vertex comes first. -/
theorem encW_cons (v : ℕ) (p : List ℕ) :
    encW (v :: p) = List.replicate v true ++ false :: encW p := by
  simp [encW]

/-- The bits of a concatenation of vertex lists. -/
theorem encW_append (p p' : List ℕ) : encW (p ++ p') = encW p ++ encW p' :=
  List.flatMap_append

/-- The empty input parses to no vertices. -/
theorem decodeW_nil : decodeW [] = some [] := by
  rw [decodeW]; simp

/-- A nonempty input whose first number is cut off. -/
theorem decodeW_of_none {w : List Bool} (hw : w ≠ []) (h : readUnaryLength w = none) :
    decodeW w = none := by
  rw [decodeW]
  simp only [hw, ite_false]
  split <;> simp_all

/-- A first number, then the rest. -/
theorem decodeW_of_some {w r : List Bool} {v : ℕ} (h : readUnaryLength w = some (v, r)) :
    decodeW w = (decodeW r).map (v :: ·) := by
  have hw : w ≠ [] := by rintro rfl; simp [readUnaryLength] at h
  rw [decodeW]
  simp only [hw, ite_false]
  split
  · simp_all
  · rename_i v' r' h'
    rw [h] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    rfl

/-- `decodeW` reads back a witness. -/
theorem decodeW_encW : ∀ p, decodeW (encW p) = some p
  | [] => decodeW_nil
  | v :: p => by
      rw [encW_cons, decodeW_of_some (readUnaryLength_replicate _ _), decodeW_encW p]
      rfl

/-- `decodeW` succeeds only on witnesses. -/
theorem encW_of_decodeW : ∀ {p : List ℕ} {w : List Bool}, decodeW w = some p → encW p = w
  | [], w, h => by
      by_cases hw : w = []
      · rw [hw]; rfl
      · cases h₁ : readUnaryLength w with
        | none => simp [decodeW_of_none hw h₁] at h
        | some q =>
            obtain ⟨v, r⟩ := q
            rw [decodeW_of_some h₁] at h
            cases decodeW r <;> simp at h
  | v :: p, w, h => by
      have hw : w ≠ [] := by rintro rfl; simp [decodeW_nil] at h
      cases h₁ : readUnaryLength w with
      | none => simp [decodeW_of_none hw h₁] at h
      | some q =>
          obtain ⟨v', r⟩ := q
          rw [decodeW_of_some h₁] at h
          cases h₂ : decodeW r with
          | none => simp [h₂] at h
          | some p' =>
              simp only [h₂, Option.map_some, Option.some.injEq, List.cons.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [(readUnaryLength_eq_some_iff _ _ _).1 h₁, encW_cons, encW_of_decodeW h₂]

/-- **The witness codec**: `decodeW` succeeds exactly on witnesses. -/
theorem decodeW_eq_some {w : List Bool} {p : List ℕ} : decodeW w = some p ↔ encW p = w :=
  ⟨encW_of_decodeW, fun h => h ▸ decodeW_encW p⟩

/-- A vertex `v` costs `v + 1` bits. -/
theorem length_encW (p : List ℕ) : (encW p).length = (p.map (· + 1)).sum := by
  induction p with
  | nil => rfl
  | cons v p ih => simp [encW_cons, ih]; omega

/-- Vertices below `n` cost at most `n` bits each. -/
theorem length_encW_le {n : ℕ} : ∀ {p : List ℕ}, (∀ v ∈ p, v < n) →
    (encW p).length ≤ p.length * n
  | [], _ => by simp
  | v :: p, h => by
      have := length_encW_le (p := p) fun u hu => h u (List.mem_cons_of_mem _ hu)
      have hv := h v List.mem_cons_self
      simp only [encW_cons, List.length_append, List.length_replicate, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- Each vertex costs at least one bit. -/
theorem length_le_length_encW (p : List ℕ) : p.length ≤ (encW p).length := by
  rw [length_encW]
  induction p with
  | nil => rfl
  | cons v p ih => simp; omega

/-! ### The check -/

/-- Consecutive vertices are arcs: listed pairs with both ends below `n`. -/
def chainOk (n : ℕ) (es : List (ℕ × ℕ)) : List ℕ → Bool
  | u :: v :: p => decide ((u, v) ∈ es ∧ u < n ∧ v < n) && chainOk n es (v :: p)
  | _ => true

/-- `chainOk` decides `List.IsChain (Path.arc n es)`. -/
theorem chainOk_iff (n : ℕ) (es : List (ℕ × ℕ)) :
    ∀ p, chainOk n es p = true ↔ p.IsChain (Path.arc n es)
  | [] => by simp [chainOk]
  | [u] => by simp [chainOk]
  | u :: v :: p => by
      rw [chainOk, Bool.and_eq_true, chainOk_iff n es (v :: p), List.isChain_cons_cons,
        decide_eq_true_eq]
      rfl

/-- The decidable form of `IsHamPath n es s t p`. -/
def hamOk (n : ℕ) (es : List (ℕ × ℕ)) (s t : ℕ) (p : List ℕ) : Bool :=
  decide p.Nodup && p.length == n && p.all (· < n) && p.head? == some s &&
    p.getLast? == some t && chainOk n es p

/-- `hamOk` decides `IsHamPath`. -/
theorem hamOk_iff {n : ℕ} {es : List (ℕ × ℕ)} {s t : ℕ} {p : List ℕ} :
    hamOk n es s t p = true ↔ IsHamPath n es s t p := by
  simp [hamOk, IsHamPath, chainOk_iff, and_assoc]

/-- The verifier: `x` is a PATH instance, `w` a witness, and the witness a Hamiltonian path. -/
def hamCheck (x w : List Bool) : Bool :=
  match Path.decodeP x, decodeW w with
  | some (s, t, n, es), some p => hamOk n es s t p
  | _, _ => false

/-- The verifier's conditions, spelled out. -/
theorem hamCheck_iff (x w : List Bool) : hamCheck x w = true ↔
    ∃ s t n es p, Path.encodeP s t n es = x ∧ encW p = w ∧ IsHamPath n es s t p := by
  constructor
  · intro h
    unfold hamCheck at h
    split at h
    · rename_i s t n es p hx hw
      exact ⟨s, t, n, es, p, Path.decodeP_eq_some.1 hx, decodeW_eq_some.1 hw, hamOk_iff.1 h⟩
    · simp at h
  · rintro ⟨s, t, n, es, p, rfl, rfl, hp⟩
    simpa [hamCheck, Path.decodeP_encodeP, decodeW_encW] using hamOk_iff.2 hp

/-- The verifier on an encoded instance and witness. -/
theorem hamCheck_encode (s t n : ℕ) (es : List (ℕ × ℕ)) (p : List ℕ) :
    hamCheck (Path.encodeP s t n es) (encW p) = hamOk n es s t p := by
  simp [hamCheck, Path.decodeP_encodeP, decodeW_encW]

/-- An instance that does not decode is rejected. -/
theorem hamCheck_of_decodeP {x : List Bool} (h : Path.decodeP x = none) (w : List Bool) :
    hamCheck x w = false := by
  simp [hamCheck, h]

/-- A witness that does not decode is rejected. -/
theorem hamCheck_of_decodeW (x : List Bool) {w : List Bool} (h : decodeW w = none) :
    hamCheck x w = false := by
  unfold hamCheck
  split <;> simp_all

/-- The length of an encoded instance. -/
theorem length_encodeP (s t n : ℕ) (es : List (ℕ × ℕ)) :
    (Path.encodeP s t n es).length = s + t + n + 3 + (Karp.edgeBits es).length := by
  simp [Path.encodeP, Karp.encodeE_eq]
  omega

/-- **HAMPATH is verified by `hamCheck`**, with witnesses of at most `(|x| + 1)²` bits. -/
theorem hamPathDec_iff (x : List Bool) :
    hamPathDec x = true ↔ ∃ w, w.length ≤ (x.length + 1) ^ 2 ∧ hamCheck x w = true := by
  simp only [hamPathDec, decide_eq_true_eq]
  constructor
  · rintro ⟨s, t, n, es, rfl, p, hp⟩
    refine ⟨encW p, ?_, (hamCheck_iff _ _).2 ⟨s, t, n, es, p, rfl, rfl, hp⟩⟩
    have h₁ := length_encW_le hp.2.2.1
    rw [hp.2.1] at h₁
    have h₂ : n ≤ (Path.encodeP s t n es).length := by rw [length_encodeP]; omega
    nlinarith
  · rintro ⟨w, -, hw⟩
    obtain ⟨s, t, n, es, p, rfl, -, hp⟩ := (hamCheck_iff x w).1 hw
    exact ⟨s, t, n, es, rfl, p, hp⟩

/-! ### The machine's view of the check -/

/-- The checks on vertex `a` (the `c`-th, after `b`, followed by `q`): `a < n`; the first vertex
is `s`, a later one follows `b` along a listed edge; `a` does not occur in `q`. -/
def stepOk (s n : ℕ) (es : List (ℕ × ℕ)) (c b a : ℕ) (q : List ℕ) : Bool :=
  decide (a < n) && (if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) && !decide (a ∈ q)

/-- The walk over the vertices `q`, after `c` vertices the last of which was `b`: every vertex
passes `stepOk`, and at the end `n` vertices were seen, at least one, the last one `t`. -/
def walkOk (s t n : ℕ) (es : List (ℕ × ℕ)) : ℕ → ℕ → List ℕ → Bool
  | c, b, [] => decide (c = n) && decide (c ≠ 0) && decide (b = t)
  | c, b, a :: q => stepOk s n es c b a q && walkOk s t n es (c + 1) a q

/-- The walk past the first vertex: the rest stays below `n`, follows listed edges from `b`,
has no repeats, brings the count to `n` and ends at `t`. -/
theorem walkOk_iff {s t n : ℕ} {es : List (ℕ × ℕ)} : ∀ (q : List ℕ) (c b : ℕ), c ≠ 0 →
    (walkOk s t n es c b q = true ↔ (∀ v ∈ q, v < n) ∧
      (b :: q).IsChain (fun u v => (u, v) ∈ es) ∧ q.Nodup ∧ c + q.length = n ∧
      (b :: q).getLast? = some t)
  | [], c, b, hc => by simp [walkOk, hc]
  | a :: q, c, b, hc => by
      rw [walkOk, Bool.and_eq_true, walkOk_iff q (c + 1) a (by omega)]
      simp only [stepOk, hc, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, List.mem_cons, forall_eq_or_imp, List.isChain_cons_cons,
        List.nodup_cons, List.length_cons, List.getLast?_cons_cons]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hq⟩, hall, hch, hnd, hlen, hl⟩
        exact ⟨⟨ha, hall⟩, ⟨hb, hch⟩, ⟨hq, hnd⟩, by omega, hl⟩
      · rintro ⟨⟨ha, hall⟩, ⟨hb, hch⟩, ⟨hq, hnd⟩, hlen, hl⟩
        exact ⟨⟨⟨ha, hb⟩, hq⟩, hall, hch, hnd, by omega, hl⟩

/-- **The machine's walk is the check**: from the start, `walkOk` decides `hamOk`. -/
theorem walkOk_eq (s t n : ℕ) (es : List (ℕ × ℕ)) :
    ∀ p, walkOk s t n es 0 0 p = hamOk n es s t p
  | [] => by simp [walkOk, hamOk]
  | a :: q => by
      rw [Bool.eq_iff_iff, hamOk_iff, walkOk, Bool.and_eq_true, walkOk_iff q 1 a one_ne_zero]
      simp only [stepOk, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, IsHamPath, List.nodup_cons, List.length_cons, List.mem_cons,
        forall_eq_or_imp, List.head?_cons, Option.some.injEq]
      have hch : ∀ (q : List ℕ), (∀ v ∈ q, v < n) →
          (q.IsChain (Path.arc n es) ↔ q.IsChain fun u v => (u, v) ∈ es) := fun q hq =>
        List.IsChain.iff_of_mem_imp fun u v hu hv =>
          ⟨fun h => h.1, fun h => ⟨h, hq u hu, hq v hv⟩⟩
      constructor
      · rintro ⟨⟨⟨ha, rfl⟩, hq⟩, hall, hc, hnd, hlen, hl⟩
        refine ⟨⟨hq, hnd⟩, by omega, ⟨ha, hall⟩, rfl, hl, ?_⟩
        exact (hch (a :: q) (by simpa using ⟨ha, hall⟩)).2 hc
      · rintro ⟨⟨hq, hnd⟩, hlen, ⟨ha, hall⟩, rfl, hl, hc⟩
        exact ⟨⟨⟨ha, rfl⟩, hq⟩, hall, (hch (a :: q) (by simpa using ⟨ha, hall⟩)).1 hc, hnd,
          by omega, hl⟩

end Cslib.Complexity.Karp.HamVerify
