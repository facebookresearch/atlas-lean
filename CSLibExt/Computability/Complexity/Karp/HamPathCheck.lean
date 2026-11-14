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

/-- **Bits of an edge list, first edge first.** For natural numbers $u, v$ and a list $E$ of pairs
of natural numbers, the bit encoding of the edge list whose first edge is $(u, v)$ and whose
remaining edges are $E$ is: $u$ copies of true, then false, then $v$ copies of true, then false,
then the bit encoding of $E$. -/
theorem edgeBits_cons (u v : ℕ) (es : List (ℕ × ℕ)) : Karp.edgeBits ((u, v) :: es) =
    List.replicate u true ++ false :: (List.replicate v true ++ false :: Karp.edgeBits es) := by
  simp [Karp.edgeBits]

/-- **Edge bits of the empty edge list.** The edge-list bit encoding of the empty list of edges
is the empty bit string. -/
@[simp] theorem edgeBits_nil : Karp.edgeBits [] = [] := rfl

/-- **Bits of concatenated edge lists.** For all lists $E$ and $E'$ of pairs of natural numbers,
the bit encoding of the concatenation of $E$ and $E'$ is the bit encoding of $E$ followed by the
bit encoding of $E'$. -/
theorem edgeBits_append (es es' : List (ℕ × ℕ)) :
    Karp.edgeBits (es ++ es') = Karp.edgeBits es ++ Karp.edgeBits es' :=
  List.flatMap_append

/-! ### Witnesses -/

/-- **Witness encoding.** The witness encoding of a list $p$ of natural numbers (the vertices of a
candidate path) is the bit string obtained by writing each entry $v$ of $p$, in order, as $v$
copies of true followed by one false, and concatenating the results. -/
def encW (p : List ℕ) : List Bool := p.flatMap fun v => List.replicate v true ++ [false]

/-- **Witness decoder.** The witness decoder reads a list $w$ of bits as a list of natural numbers.
On the empty list it returns the empty list. Otherwise it reads a unary number $v$ from the front
of $w$, a run of $v$ copies of true ended by false, and if decoding the remaining bits gives a
list $p$, it returns $v$ followed by $p$. It fails if no unary number can be read from a
nonempty list, or if decoding the remaining bits fails. -/
def decodeW (w : List Bool) : Option (List ℕ) :=
  if w = [] then some [] else
    match h : readUnaryLength w with
    | none => none
    | some (v, r) =>
        have : r.length < w.length := Karp.length_lt_of_readUnaryLength h
        (decodeW r).map (v :: ·)
termination_by w.length

/-- **Witness encoding of the empty list.** The witness encoding of the empty list of vertices is
the empty bit string. -/
@[simp] theorem encW_nil : encW [] = [] := rfl

/-- **Witness encoding of a nonempty list.** For a natural number $v$ and a list $p$ of natural
numbers, the witness encoding of the list with first entry $v$ followed by $p$ is the bit string
made of $v$ copies of true, then one false, then the witness encoding of $p$. -/
theorem encW_cons (v : ℕ) (p : List ℕ) :
    encW (v :: p) = List.replicate v true ++ false :: encW p := by
  simp [encW]

/-- **The witness encoding respects concatenation.** For lists $p$ and $p'$ of natural numbers,
the witness encoding of the concatenation of $p$ and $p'$ is the witness encoding of $p$ followed
by the witness encoding of $p'$. -/
theorem encW_append (p p' : List ℕ) : encW (p ++ p') = encW p ++ encW p' :=
  List.flatMap_append

/-- **Decoding the empty witness.** The witness decoder succeeds on the empty list of bits and
returns the empty list of vertices. -/
theorem decodeW_nil : decodeW [] = some [] := by
  rw [decodeW]; simp

/-- **Witness decoding fails on a cut-off first number.** If a list $w$ of bits is nonempty and
reading a unary number (a run of true ended by false) from the front of $w$ fails, that is, every
bit of $w$ is true, then the witness decoder fails on $w$. -/
theorem decodeW_of_none {w : List Bool} (hw : w ≠ []) (h : readUnaryLength w = none) :
    decodeW w = none := by
  rw [decodeW]
  simp only [hw, ite_false]
  split <;> simp_all

/-- **Decoding peels off the first number.** If reading a unary number from the front of a list
$w$ of bits returns $v$ with remaining bits $r$, that is, $w$ is $v$ copies of true, then false,
then $r$, then the witness decoder succeeds on $w$ exactly when it succeeds on $r$, and its
result on $w$ is $v$ followed by its result on $r$. -/
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

/-- **Decoding inverts the witness encoding.** For every list $p$ of natural numbers, the witness
decoder applied to the witness encoding of $p$ (each entry $v$ written as $v$ copies of true
followed by false) succeeds and returns $p$. -/
theorem decodeW_encW : ∀ p, decodeW (encW p) = some p
  | [] => decodeW_nil
  | v :: p => by
      rw [encW_cons, decodeW_of_some (readUnaryLength_replicate _ _), decodeW_encW p]
      rfl

/-- **The witness decoder succeeds only on encodings.** For every bit string $w$ and every list
$p$ of natural numbers, if the witness decoder returns $p$ on $w$, then $w$ is the witness
encoding of $p$. -/
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

/-- **The witness codec.** For every list $w$ of bits and every list $p$ of natural numbers, the
witness decoder returns $p$ on $w$ if and only if $w$ is the witness encoding of $p$, which
writes each entry $v$ of $p$ as $v$ copies of true followed by false. -/
theorem decodeW_eq_some {w : List Bool} {p : List ℕ} : decodeW w = some p ↔ encW p = w :=
  ⟨encW_of_decodeW, fun h => h ▸ decodeW_encW p⟩

/-- **Witness length.** For every list $p = (v_1, \dots, v_k)$ of natural numbers, the witness
encoding of $p$ has length $\sum_{i=1}^{k} (v_i + 1)$. -/
theorem length_encW (p : List ℕ) : (encW p).length = (p.map (· + 1)).sum := by
  induction p with
  | nil => rfl
  | cons v p ih => simp [encW_cons, ih]; omega

/-- **Witness length bound.** For every natural number $n$ and every list $p$ of natural numbers
all below $n$, the witness encoding of $p$ has length at most $|p| \cdot n$. -/
theorem length_encW_le {n : ℕ} : ∀ {p : List ℕ}, (∀ v ∈ p, v < n) →
    (encW p).length ≤ p.length * n
  | [], _ => by simp
  | v :: p, h => by
      have := length_encW_le (p := p) fun u hu => h u (List.mem_cons_of_mem _ hu)
      have hv := h v List.mem_cons_self
      simp only [encW_cons, List.length_append, List.length_replicate, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- **A witness is at least as long as its vertex list.** For every list $p$ of natural numbers,
the witness encoding of $p$ has length at least $|p|$. -/
theorem length_le_length_encW (p : List ℕ) : p.length ≤ (encW p).length := by
  rw [length_encW]
  induction p with
  | nil => rfl
  | cons v p ih => simp; omega

/-! ### The check -/

/-- **Arc check of a vertex list.** Given $n \in \mathbb{N}$ and a list $E$ of pairs of natural
numbers, the arc check of a list $p$ of natural numbers returns true when every two consecutive
entries $u, v$ of $p$ satisfy $(u, v) \in E$, $u < n$ and $v < n$, and false otherwise; in
particular every list with fewer than two entries passes. -/
def chainOk (n : ℕ) (es : List (ℕ × ℕ)) : List ℕ → Bool
  | u :: v :: p => decide ((u, v) ∈ es ∧ u < n ∧ v < n) && chainOk n es (v :: p)
  | _ => true

/-- **Checking a vertex list against the arcs.** For every $n \in \mathbb{N}$, every list $E$ of
pairs of natural numbers and every list $p$ of natural numbers, the arc check of $p$ against
$n$ and $E$ returns true if and only if every two consecutive entries $u, v$ of $p$ form an arc
of the digraph on $0, \dots, n - 1$ listed by $E$, that is, $(u, v) \in E$, $u < n$ and $v < n$. -/
theorem chainOk_iff (n : ℕ) (es : List (ℕ × ℕ)) :
    ∀ p, chainOk n es p = true ↔ p.IsChain (Path.arc n es)
  | [] => by simp [chainOk]
  | [u] => by simp [chainOk]
  | u :: v :: p => by
      rw [chainOk, Bool.and_eq_true, chainOk_iff n es (v :: p), List.isChain_cons_cons,
        decide_eq_true_eq]
      rfl

/-- **The Hamiltonian path check.** Given a natural number $n$, an edge list $E$, vertices $s$ and
$t$ and a list $p$ of natural numbers, the Boolean test that $p$ has no repeated entries, has
length $n$, has all entries below $n$, has first entry $s$ and last entry $t$, and that every two
consecutive entries $u, v$ of $p$ satisfy $(u, v) \in E$, $u < n$ and $v < n$. -/
def hamOk (n : ℕ) (es : List (ℕ × ℕ)) (s t : ℕ) (p : List ℕ) : Bool :=
  decide p.Nodup && p.length == n && p.all (· < n) && p.head? == some s &&
    p.getLast? == some t && chainOk n es p

/-- **The Hamiltonian path check is correct.** For all natural numbers $n$, $s$, $t$, every edge
list $E$ and every list $p$ of natural numbers, the Hamiltonian path check on $(n, E, s, t, p)$
returns true if and only if $p$ is a Hamiltonian path from $s$ to $t$ in the digraph on
$\{0, \dots, n-1\}$ with edge list $E$. -/
theorem hamOk_iff {n : ℕ} {es : List (ℕ × ℕ)} {s t : ℕ} {p : List ℕ} :
    hamOk n es s t p = true ↔ IsHamPath n es s t p := by
  simp [hamOk, IsHamPath, chainOk_iff, and_assoc]

/-- **The HAMPATH verifier.** Given bit strings $x$ and $w$, the verifier decodes $x$ as a PATH
instance, consisting of a start vertex $s$, a target vertex $t$, a vertex count $n$ and an edge
list $E$, and decodes $w$ as a witness, a list $p$ of natural numbers each written in unary. If
both decodings succeed, it accepts exactly when the Hamiltonian path check passes, that is, when
$p$ is a Hamiltonian path from $s$ to $t$ in the digraph on $\{0, \dots, n-1\}$ with edge list
$E$. If either decoding fails, it rejects. -/
def hamCheck (x w : List Bool) : Bool :=
  match Path.decodeP x, decodeW w with
  | some (s, t, n, es), some p => hamOk n es s t p
  | _, _ => false

/-- **What the HAMPATH verifier accepts.** For bit strings $x$ and $w$, the HAMPATH verifier
accepts $(x, w)$ if and only if there are natural numbers $s$, $t$, $n$, a list $es$ of pairs of
natural numbers and a list $p$ of natural numbers such that $x$ is the PATH encoding of
$(s, t, n, es)$, $w$ is the witness encoding of $p$, and $p$ is a Hamiltonian path from $s$ to $t$
in the digraph on $0, \dots, n - 1$ with edge list $es$. -/
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

/-- **The verifier on an encoded instance and witness.** For natural numbers $s$, $t$, $n$, a list
$es$ of pairs of natural numbers and a list $p$ of natural numbers, the HAMPATH verifier applied to
the PATH encoding of $(s, t, n, es)$ and the witness encoding of $p$ returns the same boolean as
the Hamiltonian path check on $n$, $es$, $s$, $t$ and $p$. -/
theorem hamCheck_encode (s t n : ℕ) (es : List (ℕ × ℕ)) (p : List ℕ) :
    hamCheck (Path.encodeP s t n es) (encW p) = hamOk n es s t p := by
  simp [hamCheck, Path.decodeP_encodeP, decodeW_encW]

/-- **Instances that do not decode are rejected.** If the PATH instance decoder fails on a bit
string $x$, then for every bit string $w$ the HAMPATH verifier rejects $(x, w)$, that is, returns
false. -/
theorem hamCheck_of_decodeP {x : List Bool} (h : Path.decodeP x = none) (w : List Bool) :
    hamCheck x w = false := by
  simp [hamCheck, h]

/-- **Witnesses that do not decode are rejected.** If the witness decoder fails on a bit string
$w$, then for every bit string $x$ the HAMPATH verifier rejects $(x, w)$, that is, returns false. -/
theorem hamCheck_of_decodeW (x : List Bool) {w : List Bool} (h : decodeW w = none) :
    hamCheck x w = false := by
  unfold hamCheck
  split <;> simp_all

/-- **Length of an encoded PATH instance.** For all natural numbers $s$, $t$, $n$ and every edge
list $E$, the encoding of the PATH instance $(s, t, n, E)$ has length $s + t + n + 3 + \ell$,
where $\ell$ is the length of the bit encoding of the edge list $E$. -/
theorem length_encodeP (s t n : ℕ) (es : List (ℕ × ℕ)) :
    (Path.encodeP s t n es).length = s + t + n + 3 + (Karp.edgeBits es).length := by
  simp [Path.encodeP, Karp.encodeE_eq]
  omega

/-- **HAMPATH is verified with quadratic-size witnesses.** For every bit string $x$, $x$ is a
yes-instance of HAMPATH if and only if there is a bit string $w$ of length at most
$(|x| + 1)^2$ such that the HAMPATH verifier accepts $(x, w)$. -/
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

/-- **One step of the HAMPATH walk.** Given natural numbers $s$ and $n$, an edge list $E$, a count
$c$ of vertices already seen, the previous vertex $b$, the current vertex $a$ and the list $q$ of
remaining vertices, the step check is true exactly when $a < n$, $a$ does not occur in $q$, and
either $c = 0$ and $a = s$, or $c \neq 0$ and $(b, a) \in E$. -/
def stepOk (s n : ℕ) (es : List (ℕ × ℕ)) (c b a : ℕ) (q : List ℕ) : Bool :=
  decide (a < n) && (if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) && !decide (a ∈ q)

/-- **The walk check of the HAMPATH verifier.** Fix natural numbers $s, t, n$ and a list $E$ of
pairs of natural numbers. The walk check accepts a list $q$ of natural numbers after $c$ vertices,
the last of which was $b$, by recursion on $q$. On the empty list it accepts if and only if
$c = n$, $c \neq 0$ and $b = t$. On a list with first entry $a$ and remaining entries $q'$ it
accepts if and only if the step check passes and the walk check accepts $q'$ after $c + 1$
vertices, the last of which was $a$. The step check requires $a < n$; it requires $a = s$ when
$c = 0$, and that $(b, a)$ is an entry of $E$ when $c \neq 0$; and it requires that $a$ does not
occur in $q'$. -/
def walkOk (s t n : ℕ) (es : List (ℕ × ℕ)) : ℕ → ℕ → List ℕ → Bool
  | c, b, [] => decide (c = n) && decide (c ≠ 0) && decide (b = t)
  | c, b, a :: q => stepOk s n es c b a q && walkOk s t n es (c + 1) a q

/-- **The walk check after the first vertex.** Let $s, t, n$ be natural numbers and $E$ a list of
pairs of natural numbers. For every list $q = (q_1, \dots, q_k)$ of natural numbers and all
natural numbers $c \neq 0$ and $b$, the walk check for $s, t, n, E$ accepts $q$ after $c$ vertices
the last of which was $b$ if and only if every $q_i$ is less than $n$, every pair $(u, v)$ of
consecutive entries of the list $(b, q_1, \dots, q_k)$ is an entry of $E$, the entries of $q$ are
pairwise distinct, $c + k = n$, and the last entry of $(b, q_1, \dots, q_k)$ is $t$. -/
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

/-- **The machine's walk is the check.** For all natural numbers $s$, $t$, $n$, every edge list
$E$ and every list $p$ of natural numbers, the walk over $p$ started with count $0$ and previous
vertex $0$ returns the same Boolean value as the Hamiltonian path check on $(n, E, s, t, p)$. -/
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
