/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `CookLevin.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/CookLevin.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.DenseSAT` namespace, `SAT` stated as a `List Bool → Prop` predicate instead of
the source repository's `Language` type, the verifier machine moved to its own module, and the
sanity examples moved to `CSLibExtTest`.
-/

module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# Dense CNF-SAT

A concrete CNF-SAT language over bit strings, `Cslib.Complexity.DenseSAT.SAT`, with the
"dense" clause encoding of `JoshuaTan42/millennium-cook-levin`, its semantics, sanity checks,
and the certificate check `check` used by the polynomial-time verifier machine
(`CSLibExt.Computability.Complexity.DenseSATVerifier`).

Encoding: a CNF is a list of *dense* clauses; a clause is a list of slots `Option Bool`
(`none` = variable absent, `some b` = literal `x_j = b`, where `j` is the slot position).
Bits are read in pairs: `00` ends a clause, `01` absent, `10` positive, `11` negative. Decoding
is total: a trailing unterminated clause and a dangling odd bit are ignored, so strings with no
`00` decode to the empty (satisfiable) formula.

This is not the binary-index encoding of `Cslib.CookLevin.encodeCNF`
(`CSLibExt/Computability/CookLevin.lean`), on which `Cslib.CookLevin.satDec` and the
`theorem_wanted` Cook-Levin statement are phrased. The dense encoding writes variable `x_j`
as slot `j` of every clause that mentions it, so the two encodings are polynomially related
only after renumbering variables; relating them needs an encoding-converter machine.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT


/-- **Dense clause.** A clause is a finite list of slots, where slot $j$ records how the variable
$x_j$ occurs: the slot is either empty (the variable is absent) or holds a Boolean $b$, meaning
the literal $x_j = b$; so $b$ true gives $x_j$ and $b$ false gives $\lnot x_j$. -/
abbrev Clause := List (Option Bool)

/-- **Dense CNF formula.** A CNF formula is a finite list of dense clauses, read as the conjunction
of its clauses. -/
abbrev CNF := List Clause

/-- **Satisfaction of a dense clause.** A finite bit sequence $a = (a_0, \dots, a_{n-1})$ satisfies
a clause $c$ when there are an index $j$ and a Boolean $b$ such that slot $j$ of $c$ holds the
literal $x_j = b$, $j < n$, and $a_j = b$. Variables $x_j$ with $j \ge n$ are unassigned and
satisfy no literal. -/
def clauseSat (c : Clause) (a : List Bool) : Prop :=
  ∃ (j : ℕ) (b : Bool), c[j]? = some (some b) ∧ a[j]? = some b

/-- **Satisfaction of a dense CNF formula.** A finite bit sequence $a$ satisfies a CNF formula
$\varphi$ when $a$ satisfies every clause of $\varphi$. -/
def cnfSat (φ : CNF) (a : List Bool) : Prop :=
  ∀ c ∈ φ, clauseSat c a

/-- **Dense decoding with an accumulator.** Given a bit string $w$ and the list $c$ of slots read so
far for the current clause, stored in reverse order, the result is the CNF formula obtained by
reading $w$ two bits at a time: $00$ outputs the current clause in reading order and continues
with no slots read; $01$ adds an empty slot to the current clause; and $1s$, for a bit $s$, adds a
slot holding the Boolean $\lnot s$, so $10$ adds a positive and $11$ a negative literal. When
fewer than two bits remain, decoding stops and outputs no further clauses, so a trailing
unterminated clause and a dangling odd bit are ignored and decoding is total. -/
def decodeAux : List Bool → Clause → CNF
  | false :: false :: r, cur => cur.reverse :: decodeAux r []
  | false :: true :: r, cur => decodeAux r (none :: cur)
  | true :: s :: r, cur => decodeAux r (some (!s) :: cur)
  | _, _ => []

/-- **Dense decoding of CNF formulas.** The CNF formula decoded from a bit string $w$ is the
result of the accumulator decoding of $w$ started with no slots read for the current clause:
$w$ is read two bits at a time, $00$ ends a clause, $01$ is an empty slot, $10$ a positive and
$11$ a negative literal, and a trailing unterminated clause and a dangling odd bit are ignored. -/
def decodeCNF (w : List Bool) : CNF := decodeAux w []

/-- **Two-bit code of a slot.** Slot $j$ of a dense clause is empty (variable $x_j$ is absent),
holds the positive literal $x_j$, or holds the negative literal $\neg x_j$. Its code is $01$ when
empty, $10$ for the positive literal and $11$ for the negative literal. -/
def encodeSlot : Option Bool → List Bool
  | none => [false, true]
  | some b => [true, !b]

/-- **Dense encoding of a clause.** The bit string encoding a clause is the concatenation of the
two-bit codes of its slots, in order (empty slot $01$, positive literal $10$, negative literal
$11$), followed by the terminator $00$. -/
def encodeClause (c : Clause) : List Bool := c.flatMap encodeSlot ++ [false, false]

/-- **Dense encoding of a CNF formula.** The dense encoding of a CNF formula $\varphi$ is the bit
string obtained by concatenating, in order, the encodings of the clauses of $\varphi$, where a
clause is encoded as the two-bit codes of its slots followed by the terminator $00$. -/
def encodeCNF (φ : CNF) : List Bool := φ.flatMap encodeClause

theorem decodeAux_slots (c : Clause) (rest : List Bool) (cur : Clause) :
    decodeAux (c.flatMap encodeSlot ++ rest) cur = decodeAux rest (c.reverse ++ cur) := by
  induction c generalizing cur with
  | nil => rfl
  | cons x c ih =>
      cases x with
      | none => simp [encodeSlot, decodeAux, ih]
      | some b => simp [encodeSlot, decodeAux, ih]

/-- **Decoding inverts the dense encoding.** For every CNF formula $\varphi$, decoding the bit
string that encodes $\varphi$ gives back $\varphi$. In particular, every CNF formula is the
decoding of some bit string. -/
theorem decodeCNF_encodeCNF (φ : CNF) : decodeCNF (encodeCNF φ) = φ := by
  unfold decodeCNF encodeCNF
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [List.flatMap_cons, encodeClause, List.append_assoc, decodeAux_slots]
      simp [decodeAux, ih]

/-- **Dense CNF-SAT.** A bit string $w$ belongs to dense CNF-SAT when the CNF formula obtained by
decoding $w$ in the dense clause encoding is satisfiable, that is, some assignment (a list of
booleans) satisfies every clause of the decoded formula. -/
def SAT (w : List Bool) : Prop := ∃ a : List Bool, cnfSat (decodeCNF w) a

/-! ### The verifier's scan, and its correctness -/

/-- **Single-pass evaluation of a dense CNF encoding.** The scan $E(r, u, v, f)$ takes the formula
bits $r$ still to be read, the assignment bits $u$ not yet used by the current clause, the bits
$v$ already used by it (most recent first) and a boolean $f$ recording whether the current clause
is already satisfied; write $x u'$ for the list with first bit $x$ followed by the list $u'$. It
reads $r$ two bits at a time; let $r'$ be the bits after the pair read. On $00$ (end of clause)
the result is $f \wedge E(r', \overline{v}\,u, [\,], \mathrm{false})$, where $\overline{v}\,u$ is
the reversal of $v$ followed by $u$. On $01$ (an empty slot) the result is $E(r', u', x v, f)$
when $u = x u'$, and $E(r', [\,], v, f)$ when $u$ is empty. On $1s$ (a literal with sign bit $s$)
the result is $E(r', u', x v, f \vee (x = \neg s))$ when $u = x u'$, and $E(r', [\,], v, f)$
when $u$ is empty. When fewer than two bits remain, the result is true.

The scan mirrors the verifier machine step by step. -/
def evalCNF : List Bool → List Bool → List Bool → Bool → Bool
  | false :: false :: r, bs, as, fl => fl && evalCNF r (as.reverse ++ bs) [] false
  | false :: true :: r, [], as, fl => evalCNF r [] as fl
  | false :: true :: r, x :: bs, as, fl => evalCNF r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => evalCNF r [] as fl
  | true :: s :: r, x :: bs, as, fl => evalCNF r bs (x :: as) (fl || x == !s)
  | _, _, _, _ => true

/-- **Indexed evaluation of a dense CNF encoding.** The scan $I(r, a, j, f)$ takes the formula
bits $r$ still to be read, an assignment $a$ (a list of booleans), the position $j$ of the next
slot in the current clause and a boolean $f$ recording whether the current clause is already
satisfied. It reads $r$ two bits at a time; let $r'$ be the bits after the pair read. On $00$
(end of clause) the result is $f \wedge I(r', a, 0, \mathrm{false})$. On $01$ (an empty slot) the
result is $I(r', a, j + 1, f)$. On $1s$ (a literal with sign bit $s$) the result is
$I(r', a, j + 1, f')$, where $f'$ is true when $f$ is true, or when $j < |a|$ and the entry $a_j$
of $a$ (counting from $0$) equals $\neg s$.
When fewer than two bits remain, the result is true. -/
def evalIdx : List Bool → List Bool → ℕ → Bool → Bool
  | false :: false :: r, a, _, fl => fl && evalIdx r a 0 false
  | false :: true :: r, a, j, fl => evalIdx r a (j + 1) fl
  | true :: s :: r, a, j, fl => evalIdx r a (j + 1) (fl || a[j]? == some (!s))
  | _, _, _, _ => true

theorem evalCNF_eq_evalIdx (r a : List Bool) (j : ℕ) (fl : Bool) :
    evalCNF r (a.drop j) (a.take j).reverse fl = evalIdx r a j fl := by
  induction r, a, j, fl using evalIdx.induct with
  | case1 r a j fl ih =>
      simp [evalCNF, evalIdx, ← ih]
  | case2 r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
  | case3 s r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
        simp
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
        simp
  | case4 r a j fl h1 h2 h3 =>
      rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalCNF, evalIdx]

theorem clauseSat_nil (a : List Bool) : ¬ clauseSat [] a := by
  rintro ⟨j, b, h, -⟩; simp at h

theorem clauseSat_append_none (c : Clause) (a : List Bool) :
    clauseSat (c ++ [none]) a ↔ clauseSat c a := by
  constructor
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact hj
    · rcases hk : j - c.length with _ | k <;> simp [hk] at hj
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]

theorem clauseSat_append_some (c : Clause) (a : List Bool) (b : Bool) :
    clauseSat (c ++ [some b]) a ↔ clauseSat c a ∨ a[c.length]? = some b := by
  constructor
  · rintro ⟨j, b', hj, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact Or.inl ⟨j, b', hj, ha⟩
    · rcases hk : j - c.length with _ | k
      · simp only [hk, List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        right
        rwa [show j = c.length by omega] at ha
      · simp [hk] at hj
  · rintro (⟨j, b', hj, ha⟩ | h)
    · refine ⟨j, b', ?_, ha⟩
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]
    · exact ⟨c.length, b, by simp, h⟩

theorem evalIdx_iff (r : List Bool) (cur : Clause) (a : List Bool) (fl : Bool)
    (hfl : fl = true ↔ clauseSat cur.reverse a) :
    evalIdx r a cur.length fl = true ↔ cnfSat (decodeAux r cur) a := by
  induction r, cur using decodeAux.induct generalizing fl with
  | case1 r cur ih =>
      have := ih false (by simp [clauseSat_nil])
      simp only [evalIdx, decodeAux, Bool.and_eq_true, cnfSat, List.mem_cons,
        forall_eq_or_imp] at this ⊢
      rw [List.length_nil] at this
      rw [this, hfl]
  | case2 r cur ih =>
      rw [evalIdx, decodeAux, ← ih fl (by rw [hfl, List.reverse_cons, clauseSat_append_none])]
      rfl
  | case3 s r cur ih =>
      rw [evalIdx, decodeAux]
      refine (Eq.to_iff rfl).trans (ih _ ?_)
      rw [List.reverse_cons, clauseSat_append_some, List.length_reverse, Bool.or_eq_true, hfl,
        beq_iff_eq]
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      have he : evalIdx r a cur.length fl = true := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalIdx]
      simp [hd, he, cnfSat]

/-- **Dense CNF-SAT certificate check.** For bit strings $w$ (the encoded formula) and $y$ (the
certificate), the check of $y$ against $w$ is the Boolean result of the verifier's left-to-right
scan of the formula bits $w$, started with $y$ as the assignment bits not yet used by the current
clause, no used bits, and the current clause not yet satisfied. -/
def check (w y : List Bool) : Bool := evalCNF w y [] false

theorem check_iff (w y : List Bool) : check w y = true ↔ cnfSat (decodeCNF w) y := by
  have h := evalCNF_eq_evalIdx w y 0 false
  simp only [List.drop_zero, List.take_zero, List.reverse_nil] at h
  rw [check, h]
  exact evalIdx_iff w [] y false (by simp [clauseSat_nil])

/-- **Decoded clauses are no longer than the input.** For every bit string $r$ and every clause
$c_0$, every clause produced by the auxiliary decoder run on $r$ with accumulated partial clause
$c_0$ has length at most $|c_0| + |r|$. -/
theorem length_le_of_mem_decodeAux (r : List Bool) (cur : Clause) :
    ∀ c ∈ decodeAux r cur, c.length ≤ cur.length + r.length := by
  induction r, cur using decodeAux.induct with
  | case1 r cur ih =>
      intro c hc
      simp only [decodeAux, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · have := ih c hc; simp at this ⊢; omega
  | case2 r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case3 s r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      simp [hd]

/-- **Truncating a satisfying assignment.** Let $w$ be a bit string and $\varphi$ the CNF formula
decoded from $w$. If a finite bit sequence $a$ satisfies $\varphi$, then so does the prefix of $a$
of length $|w|$ (all of $a$ when $a$ has at most $|w|$ bits). -/
theorem cnfSat_take (w a : List Bool) (h : cnfSat (decodeCNF w) a) :
    cnfSat (decodeCNF w) (a.take w.length) := by
  intro c hc
  obtain ⟨j, b, hj, ha⟩ := h c hc
  have hlen := length_le_of_mem_decodeAux w [] c hc
  have hjc := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨j, b, hj, ?_⟩
  rw [List.getElem?_take_of_lt (by simp at hlen; omega), ha]

/-- **Certificate characterization of dense CNF-SAT.** A bit string $w$ belongs to dense CNF-SAT
if and only if there is a bit string $y$ with $|y| \le |w|$ that the certificate check accepts
on formula bits $w$ and assignment bits $y$. -/
theorem sat_iff_check (w : List Bool) :
    SAT w ↔ ∃ y : List Bool, y.length ≤ w.length ^ 1 ∧ check w y = true := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.take w.length, by simp, (check_iff _ _).2 (cnfSat_take w a ha)⟩
  · rintro ⟨y, -, hy⟩
    exact ⟨y, (check_iff _ _).1 hy⟩

end Cslib.Complexity.DenseSAT
