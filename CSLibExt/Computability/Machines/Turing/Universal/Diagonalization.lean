/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Machines.Turing.Universal.PolyTime

/-!
# Diagonalization against time-bounded codes

Time classes for the single-tape machines of `Cslib.Turing.Universal.Code`, and the diagonal
argument from the proof of the deterministic time hierarchy theorem: for every time bound `f`,
the diagonal language `diag f` is decided by no code within `f` steps, with steps counted
exactly. Together with a polynomial-time `FinTM2` for `diag f` (`nonempty_diag_polyTime`, given a
reformatting machine; `Universal.DiagonalDecider` builds it for `f n = n ^ 2 + 1`) this
separates two models: `P ⊄ CodeTime (n ↦ n ^ 2 + 1)`. It is not Sipser's Theorem 9.10, which
separates two time bounds within one model, with a `log` factor for the simulation.

## Conventions

A code `c` *decides* `L` within `t` (`Code.DecidesWithin`) when, on every input `x`, the clocked
evaluator `c.evalSteps x (t |x|)` returns `some [bitSym (L x)]`: the machine halts within `t |x|`
steps, and the tape from the head rightwards, without trailing blanks, is exactly the symbol of
the answer bit. `CodeTime t` is the class of decision problems some code decides within `t`.
Writing the answer takes a step, so `CodeTime t` is empty when `t 0 = 0` (`codeTime_eq_empty`),
and it holds the empty language when `n + 1 ≤ t n` (`const_false_mem_codeTime`).

A bit list `x` *encodes* a code `c` when `x = Clocked.codeCells c`, the code stack that the
clocked universal machine (`Cslib.Turing.Universal.Clocked`) reads: the cells of the entries
`(q, a, q', s)` of the table, whose keys `(q, a)` strictly increase. `decodeCodeCells x` reads the
cells and the entries back and checks the keys (`Diag.cellsDecode`, `Diag.entriesOfNums`,
`Diag.keysAscendFrom`); it returns the code of the entries (`Diag.codeOfEntries`), whose code
stack is `x`, and `none` if `x` is no code stack (`isSome_decodeCodeCells_iff`). Two codes with
the same code stack have the same clocked semantics (`Code.evalSteps_eq_of_codeCells_eq`).

## The diagonal argument

`diag f x` holds iff `x` encodes a code that does not halt on `x` within `f |x|` steps with the
answer `true`. A code `c` that decided `diag f` within `f` would, on its own code stack, answer
the opposite of what `diag f` says there. Since the time classes count steps exactly, in the same
model as the diagonal language, no padding is needed (Sipser pads the encoding with `10*` because
his simulation has a constant-factor overhead), and no hypothesis on `f` is needed.

## Main definitions

- `Cslib.Turing.Universal.Code.DecidesWithin`, `Cslib.Turing.Universal.CodeTime`: deciding within
  a time bound, and the time classes on codes.
- `Cslib.Turing.Universal.Code.constFalse`: a code that answers `false` within `n + 1` steps.
- `Cslib.Turing.Universal.decodeCodeCells`, `Cslib.Turing.Universal.diag`: the code encoded by a
  bit list, and the diagonal language.
- `Cslib.Turing.Universal.diagArg`, `Cslib.Turing.Universal.diagAnswer`: the argument of the
  clocked universal function for `diag f` on `x`, and the answer read from its result.
- `Cslib.Turing.Universal.Diag.Readout.comp`: a host component that reads the answer from the
  universal machine's output.

## Main results

- `codeTime_mono`, `const_false_mem_codeTime`, `codeTime_eq_empty`: monotonicity, and when time
  classes are empty.
- `Code.evalSteps_eq_of_codeCells_eq`: the code stack determines the clocked semantics.
- `isSome_decodeCodeCells_iff`, `codeCells_of_decodeCodeCells_eq_some`: `decodeCodeCells`
  recognizes code stacks, and a decoded code has the bit list as its code stack.
- `diag_codeCells`, `diag_codeCells_eq_encOut`: `diag f` on the code stack of `c`, read from
  `c.evalSteps` and from the output `encOut` of the clocked universal machine.
- `diag_not_mem_codeTime`: **`diag f ∉ CodeTime f`**, for every `f`.
- `codeTime_ssubset_of_diag_mem`: if `f ≤ g` and `diag f ∈ CodeTime g`, then
  `CodeTime f ⊂ CodeTime g`.
- `diag_eq_comp`: `diag f = diagAnswer ∘ (clocked universal function) ∘ diagArg f`.
- `encIn_diagArg`: the universal machine's input for `diag f` on `x`, in bits.
- `nonempty_diag_polyTime`: given a polynomial-time `FinTM2` from `x` to `encIn` of
  `diagArg f x`, a polynomial-time `FinTM2` decides `diag f`.

## What is not proved here

`Cslib.Turing.Universal.DiagonalDecider` builds the reformatting machine of
`nonempty_diag_polyTime` for `f n = n ^ 2 + 1`. Not proved: the reformatting machine for other
time bounds; and the transfer back to codes, `diag f ∈ CodeTime g` for `g` polynomial in `f`,
which needs a step-counted emulation of `FinTM2` on one tape, `Code.exists_code`, and a final
tape that holds only the answer bit. Without that transfer there is no hierarchy within the code
model here.

## References

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Theorem 9.10
  (the time hierarchy theorem) and the diagonal language in its proof.
- J. Hartmanis and R. E. Stearns, *On the computational complexity of algorithms*, Trans. AMS 117
  (1965), 285–306.
-/

@[expose] public section

set_option autoImplicit false

open _root_.Turing MetaMathlibExt.ComplexityTheory

namespace Cslib.Turing.Universal

open Clocked

/-! ### Time classes on codes -/

/-- **Deciding within a time bound.** A code $c$ decides a decision problem $L$ within the time
bound $t : \mathbb{N} \to \mathbb{N}$ when, on every bit list $x$, the machine of $c$ started on the
input word of $x$ halts within $t(|x|)$ steps, and its tape from the head rightwards, without
trailing blanks, is the single symbol of the answer $L(x)$: $2$ for true and $1$ for false. -/
def Code.DecidesWithin (c : Code) (L : DecisionProblem) (t : ℕ → ℕ) : Prop :=
  ∀ x, c.evalSteps x (t x.length) = some [bitSym (L x)]

/-- **Time classes on codes.** For $t : \mathbb{N} \to \mathbb{N}$, $\mathrm{CodeTime}(t)$ is
the class of decision problems $L$ such that some code decides $L$ within $t(|x|)$ steps on
every input $x$. -/
def CodeTime (t : ℕ → ℕ) : DecisionComplexityClass :=
  {L | ∃ c : Code, c.DecidesWithin L t}

/-- **Deciding within a larger time bound.** If a code $c$ decides a decision problem $L$
within a time bound $t : \mathbb{N} \to \mathbb{N}$, and $t' : \mathbb{N} \to \mathbb{N}$
satisfies $t(n) \le t'(n)$ for every $n$, then $c$ decides $L$ within $t'$. -/
theorem Code.DecidesWithin.mono {c : Code} {L : DecisionProblem} {t t' : ℕ → ℕ}
    (h : c.DecidesWithin L t) (ht : t ≤ t') : c.DecidesWithin L t' :=
  fun x ↦ Code.evalSteps_mono (h x) (ht x.length)

/-- **Monotonicity of time classes on codes.** Let $t, t' : \mathbb{N} \to \mathbb{N}$ with
$t(n) \le t'(n)$ for every $n$. Then every decision problem that some code decides within
$t(|x|)$ steps on every input $x$ is decided by some code within $t'(|x|)$ steps on every
input $x$: $\mathrm{CodeTime}(t) \subseteq \mathrm{CodeTime}(t')$. -/
theorem codeTime_mono {t t' : ℕ → ℕ} (ht : t ≤ t') : CodeTime t ⊆ CodeTime t' :=
  fun _ ⟨c, hc⟩ ↦ ⟨c, hc.mono ht⟩

/-! ### Time classes are not empty -/

/-- **The constant-false code.** The code whose table has a single row, for state $0$: on the
blank $0$ it writes the symbol $1$, the symbol of the bit false, and enters state $1$; on the input
symbols $1$ and $2$ it moves right and stays in state $0$; on every other symbol it halts. State $1$
has no row, so the machine halts there. This code answers false on every input. -/
def Code.constFalse : Code := ⟨[[some (1, 3), some (0, 1), some (0, 1)]]⟩

/-- The run of `Code.constFalse` from the start of the rest `v` of its input. -/
private theorem constFalse_iterate (v : List Bool) (L : List ℕ) :
    Code.constFalse.stepOrStay^[v.length + 1] ⟨0, L, (input v).headI, (input v).tail⟩ =
      ⟨1, (input v).reverse ++ L, 1, []⟩ := by
  induction v generalizing L with
  | nil => rfl
  | cons b v ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : Code.constFalse.stepOrStay ⟨0, L, (input (b :: v)).headI, (input (b :: v)).tail⟩ =
        ⟨0, bitSym b :: L, (input v).headI, (input v).tail⟩ := by
      cases b <;> cases v <;> rfl
    rw [hs, ih]
    simp [input]

/-- **The constant-false code decides the empty language.** Let $c$ be the code whose table has
one row, for state $0$: on the input symbols $1$ and $2$ it moves right and stays in state $0$,
and on the blank $0$ it writes $1$, the symbol of the bit $\mathrm{false}$, and enters state
$1$, which has no row, so that $c$ halts. Then $c$ decides the empty language within $n + 1$
steps on every input of length $n$. -/
theorem Code.constFalse_decidesWithin : Code.constFalse.DecidesWithin (fun _ ↦ false) (· + 1) := by
  intro x
  rw [Code.evalSteps_eq_some_iff_output, Code.cfgAfter, Code.init, constFalse_iterate x []]
  exact ⟨rfl, rfl⟩

/-- **Time classes are not empty once the bound exceeds the input length.** Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $n + 1 \le f(n)$ for every $n$. Then the empty language, the
decision problem that answers false on every bit list, belongs to the time class of $f$: some code
decides it within $f(|x|)$ steps on every input $x$, where $|x|$ is the length of $x$. -/
theorem const_false_mem_codeTime {f : ℕ → ℕ} (hf : ∀ n, n + 1 ≤ f n) :
    (fun _ ↦ false) ∈ CodeTime f :=
  ⟨Code.constFalse, Code.constFalse_decidesWithin.mono hf⟩

/-- **Some step is needed.** Let $f : \mathbb{N} \to \mathbb{N}$ with $f(0) = 0$. Then no
decision problem is decided by a code within $f(|x|)$ steps on every input $x$: the time class
$\mathrm{CodeTime}(f)$ is empty. With no step on the empty input, the tape stays blank and
holds no answer bit. -/
theorem codeTime_eq_empty {f : ℕ → ℕ} (hf : f 0 = 0) : CodeTime f = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun L ⟨c, hc⟩ ↦ ?_
  have h := hc []
  rw [List.length_nil, hf, Code.evalSteps_eq_some_iff_output] at h
  have h0 : (c.cfgAfter [] 0).output = [] := rfl
  rw [h0] at h
  simp at h

/-! ### Code stacks determine the clocked semantics -/

/-- A cell is followed by the rest of the stack: the number and the rest are determined. -/
private theorem cell_append_inj {a b : ℕ} {r r' : List Bool} (h : cell a ++ r = cell b ++ r') :
    a = b ∧ r = r' := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [cell] using h
    | succ b => simp [cell, List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [cell, List.replicate_succ] at h
    | succ b =>
      have := ih (b := b) (by simpa [cell, List.replicate_succ] using h)
      exact ⟨by omega, this.2⟩

/-- Cells determine the numbers. -/
private theorem cells_injective : Function.Injective cells := by
  intro l l' h
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons b l' => simp [cells, cell] at h
  | cons a l ih =>
    cases l' with
    | nil => simp [cells, cell] at h
    | cons b l' =>
      simp only [cells, List.flatMap_cons] at h
      obtain ⟨rfl, h'⟩ := cell_append_inj h
      rw [ih h']

/-- The numbers of the entries determine the entries. -/
private theorem entryNums_injective : Function.Injective entryNums := by
  intro es es' h
  induction es generalizing es' with
  | nil =>
    cases es' with
    | nil => rfl
    | cons e es' => simp [entryNums] at h
  | cons e es ih =>
    cases es' with
    | nil => simp [entryNums] at h
    | cons e' es' =>
      obtain ⟨a, b, c, d⟩ := e
      obtain ⟨a', b', c', d'⟩ := e'
      simp only [entryNums, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, h⟩ := h
      rw [ih h]

/-- **The code stack determines the table lookups.** If two codes $c$ and $c'$ have the same
code stack, then for every state $q$ and every symbol $a$, the table entry of $c$ at $(q, a)$
equals the table entry of $c'$ at $(q, a)$. -/
theorem Code.lookup_eq_of_codeCells_eq {c c' : Code} (h : codeCells c = codeCells c') :
    c.lookup = c'.lookup := by
  have he : entries c = entries c' := entryNums_injective (cells_injective h)
  funext q a
  rw [← findEntry_entries, ← findEntry_entries, he]

/-- **The code stack determines the clocked semantics.** Codes with the same code stack have the
same clocked evaluator. -/
theorem Code.evalSteps_eq_of_codeCells_eq {c c' : Code} (h : codeCells c = codeCells c') :
    c.evalSteps = c'.evalSteps := by
  have hs : ∀ k, c.step k = c'.step k := fun k ↦ by
    rw [Code.step, Code.step, lookup_eq_of_codeCells_eq h]
  have hso : c.stepOrStay = c'.stepOrStay := funext fun k ↦ by
    rw [Code.stepOrStay, Code.stepOrStay, hs]
  funext x T
  simp only [Code.evalSteps, Code.cfgAfter, hso, hs]

/-- The universal machine's output encoding is injective. -/
private theorem encOut_injective : Function.Injective encOut := by
  intro o o' h
  cases o <;> cases o' <;> simp only [encOut, List.cons.injEq, reduceCtorEq, false_and,
    true_and] at h
  · rfl
  · rw [cells_injective h]

/-! ### Recognizing code stacks -/

namespace Diag

open Cslib.CookLevin

/-- A cell followed by a rest, as `Cslib.CookLevin.readUnaryLength` reads it. -/
private theorem cell_append (n : ℕ) (r : List Bool) :
    cell n ++ r = List.replicate n true ++ false :: r := by
  simp [cell]

/-- **Reading a unary length prefix reads one cell.** For bit lists $x$ and $r$ and a natural
number $n$, reading a unary length prefix of $x$ returns $n$ together with the rest $r$ if and
only if $x$ is the cell of $n$ (that is, $n$ copies of $\mathrm{true}$ followed by
$\mathrm{false}$) followed by $r$. -/
theorem readUnaryLength_eq_some_iff_cell {x r : List Bool} {n : ℕ} :
    readUnaryLength x = some (n, r) ↔ x = cell n ++ r := by
  rw [readUnaryLength_eq_some_iff, cell_append]

/-- Reading a cell shortens the list: the bound of
`Cslib.Complexity.Karp.length_lt_of_readUnaryLength`, which lives in a graph-colouring module. -/
private theorem length_lt_of_readUnaryLength {x r : List Bool} {n : ℕ}
    (h : readUnaryLength x = some (n, r)) : r.length < x.length := by
  rw [readUnaryLength_eq_some_iff_cell.1 h]
  simp [cell]
  omega

/-- **Decoding a list of cells.** For a bit list $x$, the list of natural numbers $l$ whose
cells are $x$, if there is one, and nothing otherwise. Here the cells of $l$ are its numbers
written in order, each number $n$ as $n$ copies of $\mathrm{true}$ followed by one
$\mathrm{false}$; distinct lists have distinct cells. The decoder reads one cell at a time
with the unary length reader. -/
def cellsDecode (x : List Bool) : Option (List ℕ) :=
  match x with
  | [] => some []
  | b :: x' =>
    match h : readUnaryLength (b :: x') with
    | none => none
    | some (n, r) =>
      have : r.length < (b :: x').length := by
        rw [readUnaryLength_eq_some_iff_cell.1 h]
        simp [cell]
        omega
      (cellsDecode r).map (n :: ·)
termination_by x.length

/-- **Reading entries from numbers.** A list of natural numbers is read as a list of entries
$(q, a, q', s)$, four consecutive numbers per entry, if possible: the empty list gives no entries;
a list that starts with $q, a, q', s$ and continues with $l$ gives the entry $(q, a, q', s)$
followed by the entries read from $l$, if that succeeds; and the reading fails when the length of
the list is not a multiple of $4$. -/
def entriesOfNums : List ℕ → Option (List (ℕ × ℕ × ℕ × ℕ))
  | [] => some []
  | q :: a :: q' :: s :: l => (entriesOfNums l).map ((q, a, q', s) :: ·)
  | _ => none

/-- **Ascending keys of a list of entries.** For natural numbers $p_q$, $p_a$ and a list of
entries $(q, a, q', s) \in \mathbb{N}^4$, this Boolean test is true exactly when the keys
$(q, a)$ of the entries strictly increase in lexicographic order and the first key, if there is
one, is at least $(p_q, p_a)$ in that order. -/
def keysAscendFrom (pq pa : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → Bool
  | [] => true
  | e :: es => decide (pq < e.1 ∨ pq = e.1 ∧ pa ≤ e.2.1) && keysAscendFrom e.1 (e.2.1 + 1) es

/-- **The code of a list of entries.** Let $E$ be a list of entries $(q, a, q', s)$ of natural
numbers, and let $Q$ and $M$ be the sums, over the entries of $E$ counted with multiplicity, of
$q + 1$ and of $a + 1$ respectively. The code of $E$ has a table with $Q$ rows and $M$
columns, and for $q < Q$ and $a < M$ its position $(q, a)$ holds $(q', s)$ for the first entry
$(q, a, q', s)$ of $E$ with key $(q, a)$, and is empty (halting) if $E$ has no entry with that
key. -/
def codeOfEntries (es : List (ℕ × ℕ × ℕ × ℕ)) : Code :=
  ⟨(List.range (es.map fun e ↦ e.1 + 1).sum).map fun q ↦
    (List.range (es.map fun e ↦ e.2.1 + 1).sum).map fun a ↦ findEntry q a es⟩

/-- The strict lexicographic order on the keys `(q, a)` of entries. -/
private def KeyLt (e e' : ℕ × ℕ × ℕ × ℕ) : Prop := e.1 < e'.1 ∨ e.1 = e'.1 ∧ e.2.1 < e'.2.1

/-- `cellsDecode` inverts `Clocked.cells`. -/
private theorem cellsDecode_eq_some {x : List Bool} {l : List ℕ} :
    cellsDecode x = some l ↔ x = cells l := by
  induction h : x.length using Nat.strong_induction_on generalizing x l with
  | _ len ih =>
  subst h
  match x with
  | [] =>
    rw [cellsDecode]
    cases l with
    | nil => simp [cells]
    | cons a l => simp [cells, cell]
  | b :: x' =>
    rw [cellsDecode]
    split
    · next h1 =>
      simp only [reduceCtorEq, false_iff]
      intro hx
      cases l with
      | nil => simp [cells] at hx
      | cons a l =>
        have h2 : readUnaryLength (b :: x') = some (a, cells l) :=
          readUnaryLength_eq_some_iff_cell.2 (by rw [hx]; simp [cells])
        rw [h1] at h2
        cases h2
    · next n r h1 =>
      have hx := readUnaryLength_eq_some_iff_cell.1 h1
      have hlt := length_lt_of_readUnaryLength h1
      simp only [Option.map_eq_some_iff]
      constructor
      · rintro ⟨l', hl', rfl⟩
        rw [hx, (ih _ hlt rfl).1 hl']
        simp [cells]
      · intro h
        cases l with
        | nil => simp [cells] at h
        | cons a l =>
          have h' : cell n ++ r = cell a ++ cells l := by rw [← hx, h]; simp [cells]
          obtain ⟨rfl, hr⟩ := cell_append_inj h'
          exact ⟨l, (ih _ hlt rfl).2 hr, rfl⟩

/-- `entriesOfNums` inverts `Clocked.entryNums`. -/
private theorem entriesOfNums_eq_some (l : List ℕ) (es : List (ℕ × ℕ × ℕ × ℕ)) :
    entriesOfNums l = some es ↔ l = entryNums es := by
  induction l using entriesOfNums.induct generalizing es with
  | case1 =>
    cases es with
    | nil => simp [entriesOfNums, entryNums]
    | cons e es => simp [entriesOfNums, entryNums]
  | case2 q a q' s l ih =>
    simp only [entriesOfNums, Option.map_eq_some_iff]
    constructor
    · rintro ⟨es', hes', rfl⟩
      simp [entryNums, (ih es').1 hes']
    · intro h
      cases es with
      | nil => simp [entryNums] at h
      | cons e es =>
        obtain ⟨e1, e2, e3, e4⟩ := e
        simp only [entryNums, List.flatMap_cons, List.cons_append, List.nil_append,
          List.cons.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, h⟩ := h
        exact ⟨es, (ih es).2 h, rfl⟩
  | case3 l h1 h2 =>
    have hne : entryNums es ≠ l := by
      intro h
      cases es with
      | nil => exact h1 (h ▸ rfl)
      | cons e es =>
        obtain ⟨e1, e2, e3, e4⟩ := e
        exact h2 e1 e2 e3 e4 _ (by rw [← h]; rfl)
    simp only [entriesOfNums, reduceCtorEq, false_iff]
    · exact fun h ↦ hne h.symm

/-- `keysAscendFrom` holds iff the keys strictly increase and start at `(pq, pa)` or above. -/
private theorem keysAscendFrom_iff (pq pa : ℕ) (es : List (ℕ × ℕ × ℕ × ℕ)) :
    keysAscendFrom pq pa es = true ↔
      es.Pairwise KeyLt ∧ ∀ e ∈ es, pq < e.1 ∨ pq = e.1 ∧ pa ≤ e.2.1 := by
  induction es generalizing pq pa with
  | nil => simp [keysAscendFrom]
  | cons e es ih =>
    simp only [keysAscendFrom, Bool.and_eq_true, decide_eq_true_eq, ih, List.pairwise_cons,
      List.mem_cons, forall_eq_or_imp, KeyLt]
    constructor
    · rintro ⟨he, hp, hb⟩
      refine ⟨⟨fun e' he' ↦ ?_, hp⟩, he, fun e' he' ↦ ?_⟩
      · have := hb e' he'
        omega
      · have := hb e' he'
        omega
    · rintro ⟨⟨hlt, hp⟩, he, -⟩
      refine ⟨he, hp, fun e' he' ↦ ?_⟩
      have := hlt e' he'
      omega

/-- The entries of a code have strictly increasing keys. -/
private theorem pairwise_keyLt_entries (c : Code) : (entries c).Pairwise KeyLt := by
  unfold entries
  rw [List.pairwise_flatMap]
  refine ⟨fun q _ ↦ ?_, ?_⟩
  · refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
    intro a a' hlt e he e' he'
    simp only [Option.map_eq_some_iff] at he he'
    obtain ⟨_, _, rfl⟩ := he
    obtain ⟨_, _, rfl⟩ := he'
    exact Or.inr ⟨rfl, hlt⟩
  · refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro q q' hlt e he e' he'
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at he he'
    obtain ⟨_, -, _, -, rfl⟩ := he
    obtain ⟨_, -, _, -, rfl⟩ := he'
    exact Or.inl hlt

/-- A key found by `findEntry` belongs to an entry. -/
private theorem mem_of_findEntry_eq_some {q a : ℕ} {r : ℕ × ℕ} :
    ∀ {es : List (ℕ × ℕ × ℕ × ℕ)}, findEntry q a es = some r → (q, a, r.1, r.2) ∈ es
  | [], h => by simp [findEntry] at h
  | e :: es, h => by
    simp only [findEntry] at h
    split_ifs at h with hk
    · obtain ⟨rfl, rfl⟩ := hk
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_findEntry_eq_some h)

/-- In entries with strictly increasing keys, `findEntry` finds exactly the entries. -/
private theorem findEntry_eq_some_iff {q a q' s : ℕ} :
    ∀ {es : List (ℕ × ℕ × ℕ × ℕ)}, es.Pairwise KeyLt →
      (findEntry q a es = some (q', s) ↔ (q, a, q', s) ∈ es)
  | [], _ => by simp [findEntry]
  | e :: es, hp => by
    rw [List.pairwise_cons] at hp
    refine ⟨fun h ↦ mem_of_findEntry_eq_some h, fun h ↦ ?_⟩
    simp only [findEntry]
    split_ifs with hk
    · rcases List.mem_cons.1 h with rfl | h
      · rfl
      · have := hp.1 _ h
        simp only [KeyLt] at this
        omega
    · rcases List.mem_cons.1 h with rfl | h
      · exact absurd ⟨rfl, rfl⟩ hk
      · exact (findEntry_eq_some_iff hp.2).2 h

/-- **Entries with strictly increasing keys are the entries of their code.** -/
private theorem entries_codeOfEntries {es : List (ℕ × ℕ × ℕ × ℕ)} (hp : es.Pairwise KeyLt) :
    entries (codeOfEntries es) = es := by
  set Q := (es.map fun e ↦ e.1 + 1).sum
  set M := (es.map fun e ↦ e.2.1 + 1).sum
  set c := codeOfEntries es
  have htab : c.table = (List.range Q).map fun q ↦ (List.range M).map fun a ↦ findEntry q a es :=
    rfl
  have hlook : ∀ q a, c.lookup q a = findEntry q a es := by
    intro q a
    have hbound : ∀ r, findEntry q a es = some r → q < Q ∧ a < M := fun r h ↦ by
      have hm := mem_of_findEntry_eq_some h
      have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun e ↦ e.1 + 1) hm)
      have h2 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun e ↦ e.2.1 + 1) hm)
      exact ⟨by simp only at h1; omega, by simp only at h2; omega⟩
    have hnone : ¬(q < Q ∧ a < M) → findEntry q a es = none := fun h ↦ by
      cases hr : findEntry q a es with
      | none => rfl
      | some r => exact absurd (hbound r hr) h
    by_cases hq : q < Q
    · by_cases ha : a < M
      · simp only [Code.lookup, htab, List.getElem?_map, List.getElem?_range hq,
          Option.map_some, Option.bind_some, List.getElem?_range ha, Option.join_some]
      · simp only [Code.lookup, htab, List.getElem?_map, List.getElem?_range hq,
          Option.map_some, Option.bind_some,
          List.getElem?_eq_none (l := List.range M) (by simpa using ha), Option.map_none,
          Option.join_none, hnone (fun h ↦ ha h.2)]
    · simp only [Code.lookup, htab, List.getElem?_map,
        List.getElem?_eq_none (l := List.range Q) (by simpa using hq), Option.map_none,
        Option.bind_none, Option.join_none, hnone (fun h ↦ hq h.1)]
  have hpc := pairwise_keyLt_entries c
  have hmem : ∀ e, e ∈ entries c ↔ e ∈ es := by
    rintro ⟨q, a, q', s⟩
    rw [← findEntry_eq_some_iff hpc, ← findEntry_eq_some_iff hp, findEntry_entries, hlook]
  have hnd : ∀ {l : List (ℕ × ℕ × ℕ × ℕ)}, l.Pairwise KeyLt → l.Nodup := fun h ↦
    h.imp fun h' he ↦ by subst he; simp only [KeyLt] at h'; omega
  refine List.Perm.eq_of_pairwise (le := KeyLt) (fun e e' _ _ h h' ↦ ?_) hpc hp
    ((List.perm_ext_iff_of_nodup (hnd hpc) (hnd hp)).2 hmem)
  simp only [KeyLt] at h h'
  omega

end Diag

open Diag

/-! ### The diagonal language -/

/-- **Decoding a code stack.** For a bit list $x$, the decoding of $x$ as a code is defined as
follows. Write the cell of a number $n$ for the $n$ bits true followed by one bit false, and the
cells of a list of numbers for the cells of its numbers in order. If $x$ is the cells of a list
$l$ of natural numbers (such an $l$ is unique), the length of $l$ is a multiple of $4$, and the
keys $(q, a)$ of the entries $(q, a, q', s)$ formed by the consecutive groups of four numbers of
$l$ strictly increase in lexicographic order, then the decoding of $x$ is the code of these
entries. Otherwise the decoding returns no code.

The code stack of a code is the cells of the numbers $q, a, q', s$ of its entries
$(q, a, q', s)$, listed by increasing key $(q, a)$; codes with the same code stack have the same
clocked evaluator. -/
def decodeCodeCells (x : List Bool) : Option Code :=
  ((cellsDecode x).bind entriesOfNums).bind fun es ↦
    if keysAscendFrom 0 0 es then some (codeOfEntries es) else none

/-- **The diagonal language.** For $f : \mathbb{N} \to \mathbb{N}$, the diagonal language of $f$
holds at a bit list $x$ iff $x$ encodes a code $c$ and the clocked evaluator, running $c$ on $x$
for at most $f(|x|)$ steps, does not return the output $[2]$, the symbol of the answer true:
either $c$ does not halt on $x$ within $f(|x|)$ steps, or it halts with another output. Bit lists
that encode no code are not in the language. This is the diagonal language of the proof of
Sipser's Theorem 9.10. -/
def diag (f : ℕ → ℕ) : DecisionProblem := fun x ↦
  match decodeCodeCells x with
  | none => false
  | some c => decide (c.evalSteps x (f x.length) ≠ some [bitSym true])

/-- **Decoding inverts the code stack.** For every bit list $x$ and every code $c$, if $x$
decodes to $c$, then the code stack of $c$ is $x$. -/
theorem codeCells_of_decodeCodeCells_eq_some {x : List Bool} {c : Code}
    (h : decodeCodeCells x = some c) :
    codeCells c = x := by
  simp only [decodeCodeCells, Option.bind_eq_some_iff, cellsDecode_eq_some, entriesOfNums_eq_some,
    Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨es, ⟨l, rfl, rfl⟩, hk, rfl⟩ := h
  rw [codeCells, entries_codeOfEntries ((keysAscendFrom_iff 0 0 es).1 hk).1]

/-- **Code stacks are recognized.** For every bit list $x$, the decoding of $x$ as a code
succeeds iff $x$ is the code stack of some code. -/
theorem isSome_decodeCodeCells_iff (x : List Bool) :
    (decodeCodeCells x).isSome ↔ ∃ c : Code, codeCells c = x := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
    exact ⟨c, codeCells_of_decodeCodeCells_eq_some hc⟩
  · rintro ⟨c, rfl⟩
    have hk : keysAscendFrom 0 0 (entries c) = true :=
      (keysAscendFrom_iff 0 0 _).2 ⟨pairwise_keyLt_entries c, fun e _ ↦ by omega⟩
    have h1 : cellsDecode (codeCells c) = some (entryNums (entries c)) := cellsDecode_eq_some.2 rfl
    have h2 : entriesOfNums (entryNums (entries c)) = some (entries c) :=
      (entriesOfNums_eq_some _ _).2 rfl
    have hd : decodeCodeCells (codeCells c) = some (codeOfEntries (entries c)) := by
      simp only [decodeCodeCells, h1, Option.bind_some, h2, hk, ↓reduceIte]
    rw [hd]
    rfl

/-- **Code stacks, entry by entry.** A bit list $x$ encodes a code (its decoding succeeds) iff
there is a list of entries $(q, a, q', s)$ of natural numbers whose keys $(q, a)$ strictly
increase in lexicographic order, such that $x$ is the list of cells of the numbers of these
entries, four numbers per entry. -/
theorem isSome_decodeCodeCells_iff_entries (x : List Bool) : (decodeCodeCells x).isSome ↔
    ∃ es, x = cells (entryNums es) ∧ keysAscendFrom 0 0 es = true := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
    simp only [decodeCodeCells, Option.bind_eq_some_iff, cellsDecode_eq_some, entriesOfNums_eq_some,
      Option.ite_none_right_eq_some, Option.some.injEq] at hc
    obtain ⟨es, ⟨l, rfl, rfl⟩, hk, -⟩ := hc
    exact ⟨es, rfl, hk⟩
  · rintro ⟨es, rfl, hk⟩
    have h1 : cellsDecode (cells (entryNums es)) = some (entryNums es) := cellsDecode_eq_some.2 rfl
    have h2 : entriesOfNums (entryNums es) = some es := (entriesOfNums_eq_some _ _).2 rfl
    simp only [decodeCodeCells, h1, Option.bind_some, h2, hk, ↓reduceIte, Option.isSome_some]

/-- **Code stacks decode to codes with the same code stack.** For every code $c$, decoding the code
stack of $c$ succeeds and returns a code $c'$ whose code stack equals the code stack of $c$. -/
theorem decodeCodeCells_codeCells (c : Code) :
    ∃ c', decodeCodeCells (codeCells c) = some c' ∧ codeCells c' = codeCells c := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 ((isSome_decodeCodeCells_iff _).2 ⟨c, rfl⟩)
  exact ⟨c', hc', codeCells_of_decodeCodeCells_eq_some hc'⟩

/-- **The diagonal language on a code stack.** For every time bound
$f : \mathbb{N} \to \mathbb{N}$ and every code $c$ with code stack $x$, the bit list $x$ belongs to
the diagonal language for $f$ iff it is not the case that $c$, run on $x$, halts within $f(|x|)$
steps with output the single symbol $2$ of the bit true. -/
theorem diag_codeCells (f : ℕ → ℕ) (c : Code) :
    diag f (codeCells c) =
      decide (c.evalSteps (codeCells c) (f (codeCells c).length) ≠ some [bitSym true]) := by
  obtain ⟨c', hd, hc'⟩ := decodeCodeCells_codeCells c
  simp only [diag, hd, Code.evalSteps_eq_of_codeCells_eq hc']

/-- **Bit lists that encode no code are outside the diagonal language.** For every
$f : \mathbb{N} \to \mathbb{N}$ and every bit list $x$ that is the code stack of no code, $x$ is not
in the diagonal language of $f$. -/
theorem diag_eq_false {f : ℕ → ℕ} {x : List Bool} (hx : ∀ c : Code, codeCells c ≠ x) :
    diag f x = false := by
  have hd : decodeCodeCells x = none := by
    cases h : decodeCodeCells x with
    | none => rfl
    | some c => exact absurd (codeCells_of_decodeCodeCells_eq_some h) (hx c)
  simp only [diag, hd]

/-- **The diagonal language through the universal machine.** For every time bound
$f : \mathbb{N} \to \mathbb{N}$ and every code $c$ with code stack $x$, the bit list $x$ belongs to
the diagonal language for $f$ iff the output encoding of the result of running $c$ on $x$ for at
most $f(|x|)$ steps differs from the output encoding of the result whose output is the single
symbol $2$ of the bit true.

The clocked universal machine reads the input encoding of a code, an input and a clock $T$ and
writes the output encoding of the result of running the code on the input for at most $T$ steps,
so the condition is read from its output on $c$, $x$ and $f(|x|)$. -/
theorem diag_codeCells_eq_encOut (f : ℕ → ℕ) (c : Code) :
    diag f (codeCells c) = decide
      (encOut (c.evalSteps (codeCells c) (f (codeCells c).length)) ≠
        encOut (some [bitSym true])) := by
  rw [diag_codeCells]
  simp only [ne_eq, encOut_injective.eq_iff]

/-- **The diagonal argument.** For every $f : \mathbb{N} \to \mathbb{N}$, the diagonal language of
$f$ is not in the time class of $f$ on codes: no code decides it on every input $x$ within
$f(|x|)$ steps. This is the argument from the proof of Sipser's Theorem 9.10: a code $c$ deciding
it would, on its own code stack, answer the opposite of the diagonal language of $f$. -/
theorem diag_not_mem_codeTime (f : ℕ → ℕ) : diag f ∉ CodeTime f := by
  rintro ⟨c, hc⟩
  have h := hc (codeCells c)
  have hd := diag_codeCells f c
  cases hb : diag f (codeCells c)
  · rw [hb] at h hd
    rw [eq_comm, decide_eq_false_iff_not, not_not] at hd
    rw [hd] at h
    simp [bitSym] at h
  · rw [hb] at h hd
    rw [eq_comm, decide_eq_true_iff] at hd
    exact hd h

/-- **A hierarchy within codes, given an upper bound.** Let $f, g : \mathbb{N} \to \mathbb{N}$
with $f(n) \le g(n)$ for every $n$, and for a time bound $t$ let $\mathrm{CodeTime}(t)$ be the
class of decision problems that some code decides within $t(|x|)$ steps on every input $x$.
If the diagonal language $\mathrm{diag}(f)$ belongs to $\mathrm{CodeTime}(g)$, then
$\mathrm{CodeTime}(f)$ is a proper subclass of $\mathrm{CodeTime}(g)$. -/
theorem codeTime_ssubset_of_diag_mem {f g : ℕ → ℕ} (hfg : f ≤ g) (h : diag f ∈ CodeTime g) :
    CodeTime f ⊂ CodeTime g :=
  (Set.ssubset_iff_of_subset (codeTime_mono hfg)).2 ⟨diag f, h, diag_not_mem_codeTime f⟩

/-! ### The upper bound, up to the reformatting machine -/

/-- **The universal machine's argument for the diagonal language.** For a time bound
$f : \mathbb{N} \to \mathbb{N}$ and a bit list $x$, the argument is a triple of a code, an input and
a clock. If $x$ decodes to a code $c$, it is $(c, x, f(|x|))$. Otherwise it is the code with the
empty table, the input consisting of the single bit true, and the clock $0$; that code halts at
once with the answer true, so that the diagonal answer is false there. -/
def diagArg (f : ℕ → ℕ) (x : List Bool) : Code × List Bool × ℕ :=
  match decodeCodeCells x with
  | some c => (c, x, f x.length)
  | none => (⟨[]⟩, [true], 0)

/-- **The reformatting function in bits.** For $f : \mathbb{N} \to \mathbb{N}$ and a bit list $x$,
the input bits of the clocked universal machine on its argument for the diagonal language of $f$
on $x$ are, when $x$ encodes a code, the cell of $f(|x|)$, then the cells of the input symbols of
$x$, then the bit false, then $x$ reversed; when $x$ encodes no code, they are the fixed list
$[\mathrm{false}, \mathrm{true}, \mathrm{true}, \mathrm{false}, \mathrm{false}]$. -/
theorem encIn_diagArg (f : ℕ → ℕ) (x : List Bool) :
    encIn (diagArg f x).1 (diagArg f x).2.1 (diagArg f x).2.2 =
      if (decodeCodeCells x).isSome then
        cell (f x.length) ++ (cells (input x) ++ (false :: x.reverse))
      else [false, true, true, false, false] := by
  rcases hd : decodeCodeCells x with _ | c
  · simp only [diagArg, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    decide
  · simp only [diagArg, hd, Option.isSome_some, ↓reduceIte, encIn,
      codeCells_of_decodeCodeCells_eq_some hd]

/-- **The diagonal answer.** For a clocked result $o$, either a timeout or the output of a halted
run, the diagonal answer of $o$ is false if $o$ is the output consisting of the single symbol $2$,
the symbol of the bit true, and true otherwise, including on a timeout. -/
def diagAnswer (o : Option (List ℕ)) : Bool := decide (o ≠ some [bitSym true])

/-- **The diagonal answer read from the encoded output.** For every clocked result $o$, either a
timeout or the output of a halted run, the diagonal answer of $o$ is true exactly when the output
encoding of $o$ differs from the output encoding of the result whose output is the single symbol
$2$ of the bit true, which is the bit list true, true, true, false. -/
theorem diagAnswer_eq_decide_encOut (o : Option (List ℕ)) :
    diagAnswer o = decide (encOut o ≠ encOut (some [bitSym true])) := by
  simp only [diagAnswer, ne_eq, encOut_injective.eq_iff]

/-- **The diagonal language through the clocked evaluator.** For every
$f : \mathbb{N} \to \mathbb{N}$ and every bit list $x$, let $(c, y, T)$ be the universal machine's
argument for the diagonal language of $f$ on $x$. Then the diagonal language of $f$ holds at $x$
iff the clocked evaluator, running $c$ on $y$ for at most $T$ steps, does not return the output
$[2]$, the symbol of the answer true. -/
theorem diag_eq_comp (f : ℕ → ℕ) :
    diag f = diagAnswer ∘ (fun a : Code × List Bool × ℕ ↦ a.1.evalSteps a.2.1 a.2.2) ∘
      diagArg f := by
  funext x
  have h0 : Code.evalSteps ⟨[]⟩ [true] 0 = some [bitSym true] := by decide
  rcases hd : decodeCodeCells x with _ | c <;> simp [diag, diagArg, diagAnswer, hd, h0]

namespace Diag.Readout

open Function MetaMathlibExt.TM2Program

/-- **Stacks of the readout machine.** The readout machine, which reads the answer of the
diagonal language off the output of the clocked universal machine, has exactly two stacks: the
input stack $X$ and the output stack $O$. -/
inductive K | X | O
  deriving DecidableEq

/-- Finitely many stacks. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .O], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the readout machine.** The readout machine has eight labels: $r_0$, $r_1$,
$r_2$ and $r_3$ read in turn the bits $\mathrm{true}, \mathrm{true}, \mathrm{true},
\mathrm{false}$, which encode, at the output of the clocked universal machine, a halt whose
output is the single symbol of the bit $\mathrm{true}$; $r_4$ checks that no bit follows;
$\mathrm{hit}$ and $\mathrm{miss}$ write the answer; and $\mathrm{done}$ stops. -/
inductive Lab | r0 | r1 | r2 | r3 | r4 | hit | miss | done
  deriving DecidableEq

/-- Finitely many labels. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.r0, .r1, .r2, .r3, .r4, .hit, .miss, .done], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack alphabet of the readout machine.** Every stack of the readout machine, namely
the input stack $X$ and the output stack $O$, has the alphabet of bits. -/
abbrev Γ : K → Type := fun _ => Bool

/-- **Expecting a bit in the readout machine.** For a bit $b$ and a label $\ell$, the statement
that pops the top of the input stack $X$ and goes to $\ell$ if the popped symbol is $b$, and to the
label miss otherwise, including when $X$ is empty. -/
def expect (b : Bool) (next : Lab) : TM2.Stmt Γ Lab Bool :=
  .pop .X (fun _ o ↦ o == some b) (.branch id (.goto fun _ ↦ next) (.goto fun _ ↦ .miss))

/-- **Program of the readout machine.** The readout machine pops the bits of its input stack
$X$ one at a time and compares them with $\mathrm{true}, \mathrm{true}, \mathrm{true},
\mathrm{false}$, which encode, at the output of the clocked universal machine, a halt whose
output is the single symbol of the bit $\mathrm{true}$. If the input is exactly this list, it
pushes $\mathrm{false}$ onto its output stack $O$; otherwise (at the first bit that differs,
when the input ends early, or when a fifth bit follows) it pushes $\mathrm{true}$. Then it
halts. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .r0 => expect true .r1
  | .r1 => expect true .r2
  | .r2 => expect true .r3
  | .r3 => expect false .r4
  | .r4 => .pop .X (fun _ o ↦ o.isNone) (.branch id (.goto fun _ ↦ .hit) (.goto fun _ ↦ .miss))
  | .hit => .push .O (fun _ ↦ false) (.goto fun _ ↦ .done)
  | .miss => .push .O (fun _ ↦ true) (.goto fun _ ↦ .done)
  | .done => .halt

/-- **The readout machine as a host component.** The component machine whose stacks are the
input $X$ and the output $O$, each over the alphabet of bits, whose labels and program are
those of the readout machine, which checks whether $X$ holds exactly
$(\mathrm{true}, \mathrm{true}, \mathrm{true}, \mathrm{false})$ and pushes $\mathrm{false}$ on
$O$ if so and $\mathrm{true}$ otherwise, and whose list of stacks is $(X, O)$. -/
abbrev comp : Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ := fun _ ↦ inferInstanceAs (Fintype Bool)
  L := Lab
  prog := prog
  ks := [.X, .O]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **The readout run.** Let $l$ be a bit list, and start the readout machine at the label
$r_0$ with its internal Boolean variable set to $\mathrm{false}$, $l$ on the input stack $X$ and
the output stack $O$ empty. Then the machine reaches the label $\mathrm{done}$ within $6$ steps,
and $O$ then holds exactly one bit, which is $\mathrm{true}$ if and only if
$l \ne [\mathrm{true}, \mathrm{true}, \mathrm{true}, \mathrm{false}]$, the list that encodes, at
the output of the clocked universal machine, a halt whose output is the single symbol of the bit
$\mathrm{true}$. -/
theorem run (l : List Bool) :
    ∃ v S', RunLe prog 6 ⟨some .r0, false, update (fun _ ↦ []) .X l⟩ ⟨some .done, v, S'⟩ ∧
      S' .O = [decide (l ≠ encOut (some [bitSym true]))] := by
  rcases l with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨b, l⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, ⟨2, by norm_num, rfl⟩, rfl⟩
    | exact ⟨_, _, ⟨3, by norm_num, rfl⟩, rfl⟩
    | exact ⟨_, _, ⟨4, by norm_num, rfl⟩, rfl⟩
    | exact ⟨_, _, ⟨5, by norm_num, rfl⟩, rfl⟩
    | exact ⟨_, _, ⟨6, le_rfl, rfl⟩, rfl⟩

/-- **The readout on raw bits in polynomial time.** A finite multi-stack Turing machine, whose
input and output alphabets are identified with the bits, together with a polynomial time bound,
such that for every bit list $l$, given $l$ as its input, it halts within the bound, evaluated at
$|l|$, with output the one-bit list $[b]$, where $b$ is true if and only if $l$ differs from the
output encoding of the result whose output is the single symbol $2$ of the bit true, that is,
from the list true, true, true, false. -/
noncomputable def bitsPolyTime :
    TM2ComputableInPolyTime (fun l : List Bool ↦ l) (fun l : List Bool ↦ l)
      (fun l ↦ [decide (l ≠ encOut (some [bitSym true]))]) :=
  Complexity.Host.reduction (c := comp) (cX := .X) (cO := .O) (gX := id) (start := .r0)
    (done := .done) (Equiv.refl Bool) _ (Polynomial.C 6) rfl fun l ↦ by
      obtain ⟨v, S', hr, hO⟩ := run l
      exact ⟨v, S', by simpa using hr, by simpa using hO⟩

/-- **The readout in polynomial time.** A finite multi-stack Turing machine, given the output
encoding $\mathrm{encOut}(o)$ of a result $o$ of the clocked universal function (a list of
symbols, or a timeout), outputs the one-bit list $[\mathrm{diagAnswer}(o)]$ within a number
of steps polynomial in the length of $\mathrm{encOut}(o)$. Here $\mathrm{diagAnswer}(o)$ is
$\mathrm{true}$ unless $o$ is a halt whose output is the single symbol of the bit
$\mathrm{true}$. -/
noncomputable def polyTime : TM2ComputableInPolyTime encOut (fun b : Bool ↦ [b]) diagAnswer where
  toTM2ComputableAux := bitsPolyTime.toTM2ComputableAux
  time := bitsPolyTime.time
  outputsFun o := by
    have h := bitsPolyTime.outputsFun (encOut o)
    rwa [← diagAnswer_eq_decide_encOut] at h

end Diag.Readout

/-- **The diagonal language in polynomial time, given the reformatting machine.** Let
$f : \mathbb{N} \to \mathbb{N}$. Suppose that a finite multi-stack Turing machine, the
reformatting machine, computes in polynomial time, from a bit list $x$ given as itself, the
input $\mathrm{encIn}(c, y, T)$ of the clocked universal machine, where
$(c, y, T) = \mathrm{diagArg}_f(x)$ is the argument of the clocked universal function for the
diagonal language $\mathrm{diag}_f$ on $x$. Then a finite multi-stack Turing machine computes
$\mathrm{diag}_f$ in polynomial time: on every bit list $x$, given as itself, it outputs the
one-bit list $[\mathrm{diag}_f(x)]$.

The machine runs the reformatting machine, then the clocked universal machine, then the
readout machine. -/
theorem nonempty_diag_polyTime {f : ℕ → ℕ}
    (hR : TM2ComputableInPolyTime (fun x : List Bool ↦ x)
      (fun a : Code × List Bool × ℕ ↦ encIn a.1 a.2.1 a.2.2) (diagArg f)) :
    Nonempty (TM2ComputableInPolyTime (fun x : List Bool ↦ x) (fun b : Bool ↦ [b]) (diag f)) := by
  obtain ⟨U⟩ := nonempty_univPolyTime
  have h := MetaMathlibExt.TM2Composition.compComputable
    (MetaMathlibExt.TM2Composition.compComputable hR U) Diag.Readout.polyTime
  rw [← diag_eq_comp] at h
  exact ⟨h⟩

end Cslib.Turing.Universal
