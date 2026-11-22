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

/-- `c.DecidesWithin L t`: on every input `x`, the code `c` halts within `t |x|` steps, and the
tape from the head rightwards, without trailing blanks, is the symbol `bitSym (L x)` of the
answer. -/
def Code.DecidesWithin (c : Code) (L : DecisionProblem) (t : ℕ → ℕ) : Prop :=
  ∀ x, c.evalSteps x (t x.length) = some [bitSym (L x)]

/-- `CodeTime t`: the decision problems that some code decides within `t |x|` steps on every
input `x`. -/
def CodeTime (t : ℕ → ℕ) : DecisionComplexityClass :=
  {L | ∃ c : Code, c.DecidesWithin L t}

/-- A code that decides `L` within `t` decides it within every larger bound. -/
theorem Code.DecidesWithin.mono {c : Code} {L : DecisionProblem} {t t' : ℕ → ℕ}
    (h : c.DecidesWithin L t) (ht : t ≤ t') : c.DecidesWithin L t' :=
  fun x ↦ Code.evalSteps_mono (h x) (ht x.length)

/-- **Monotonicity.** Time classes grow with the time bound. -/
theorem codeTime_mono {t t' : ℕ → ℕ} (ht : t ≤ t') : CodeTime t ⊆ CodeTime t' :=
  fun _ ⟨c, hc⟩ ↦ ⟨c, hc.mono ht⟩

/-! ### Time classes are not empty -/

/-- A code that answers `false` on every input: in state `0` it moves right over the input
symbols `1` and `2`, and on the first blank it writes `bitSym false = 1` and enters the state
`1`, which has no row and so halts. -/
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

/-- `Code.constFalse` decides the empty language within `n + 1` steps. -/
theorem Code.constFalse_decidesWithin : Code.constFalse.DecidesWithin (fun _ ↦ false) (· + 1) := by
  intro x
  rw [Code.evalSteps_eq_some_iff_output, Code.cfgAfter, Code.init, constFalse_iterate x []]
  exact ⟨rfl, rfl⟩

/-- **Time classes are not empty**: the empty language is in `CodeTime f` as soon as
`n + 1 ≤ f n`. -/
theorem const_false_mem_codeTime {f : ℕ → ℕ} (hf : ∀ n, n + 1 ≤ f n) :
    (fun _ ↦ false) ∈ CodeTime f :=
  ⟨Code.constFalse, Code.constFalse_decidesWithin.mono hf⟩

/-- **Some step is needed.** `CodeTime f` is empty when `f 0 = 0`: with no step on the empty
input, the tape stays blank and holds no answer bit. -/
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

/-- Codes with the same code stack have the same table lookups. -/
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

/-- `readUnaryLength` reads one cell. -/
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

/-- The numbers whose cells are the bit list, if any: the inverse of `Clocked.cells`, reading one
cell at a time with `Cslib.CookLevin.readUnaryLength`. -/
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

/-- The entries whose numbers are the list, four numbers per entry, if any: the inverse of
`Clocked.entryNums`. -/
def entriesOfNums : List ℕ → Option (List (ℕ × ℕ × ℕ × ℕ))
  | [] => some []
  | q :: a :: q' :: s :: l => (entriesOfNums l).map ((q, a, q', s) :: ·)
  | _ => none

/-- `keysAscendFrom pq pa es`: the keys `(q, a)` of the entries strictly increase in
lexicographic order, starting at `(pq, pa)` or above. -/
def keysAscendFrom (pq pa : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → Bool
  | [] => true
  | e :: es => decide (pq < e.1 ∨ pq = e.1 ∧ pa ≤ e.2.1) && keysAscendFrom e.1 (e.2.1 + 1) es

/-- The code of a list of entries: its table has a row for every state and a column for every
symbol below the sums of the states and the symbols of the entries plus one, and each position
holds the first entry with its key (`Clocked.findEntry`). -/
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

/-- The code encoded by the bits `x`: if `x` is a code stack (`Clocked.codeCells`, the code as
the clocked universal machine reads it), that is, the cells of entries `(q, a, q', s)` whose
keys `(q, a)` strictly increase, the code of these entries (`codeOfEntries`); `none` otherwise.
Codes with the same code stack have the same clocked semantics
(`Code.evalSteps_eq_of_codeCells_eq`). -/
def decodeCodeCells (x : List Bool) : Option Code :=
  ((cellsDecode x).bind entriesOfNums).bind fun es ↦
    if keysAscendFrom 0 0 es then some (codeOfEntries es) else none

/-- **The diagonal language** (Sipser, proof of Theorem 9.10): `diag f x` holds iff `x` encodes a
code (`decodeCodeCells`) that does not halt on `x` within `f |x|` steps with the answer `true`.
Bit lists that encode no code are not in the language. -/
def diag (f : ℕ → ℕ) : DecisionProblem := fun x ↦
  match decodeCodeCells x with
  | none => false
  | some c => decide (c.evalSteps x (f x.length) ≠ some [bitSym true])

/-- A decoded code has the bit list as its code stack. -/
theorem codeCells_of_decodeCodeCells_eq_some {x : List Bool} {c : Code}
    (h : decodeCodeCells x = some c) :
    codeCells c = x := by
  simp only [decodeCodeCells, Option.bind_eq_some_iff, cellsDecode_eq_some, entriesOfNums_eq_some,
    Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨es, ⟨l, rfl, rfl⟩, hk, rfl⟩ := h
  rw [codeCells, entries_codeOfEntries ((keysAscendFrom_iff 0 0 es).1 hk).1]

/-- **Code stacks are recognized.** `decodeCodeCells x` is defined iff `x` is the code stack of a
code. -/
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

/-- **Code stacks, entry by entry.** `decodeCodeCells x` is defined iff `x` is the cells of the
numbers of entries whose keys strictly increase. -/
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

/-- Every code stack decodes to a code with that code stack. -/
theorem decodeCodeCells_codeCells (c : Code) :
    ∃ c', decodeCodeCells (codeCells c) = some c' ∧ codeCells c' = codeCells c := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 ((isSome_decodeCodeCells_iff _).2 ⟨c, rfl⟩)
  exact ⟨c', hc', codeCells_of_decodeCodeCells_eq_some hc'⟩

/-- **The diagonal language on a code stack.** On the code stack of `c`, `diag f` holds iff `c`
does not halt there within `f` steps with the answer `true`. -/
theorem diag_codeCells (f : ℕ → ℕ) (c : Code) :
    diag f (codeCells c) =
      decide (c.evalSteps (codeCells c) (f (codeCells c).length) ≠ some [bitSym true]) := by
  obtain ⟨c', hd, hc'⟩ := decodeCodeCells_codeCells c
  simp only [diag, hd, Code.evalSteps_eq_of_codeCells_eq hc']

/-- Bit lists that are no code stack are not in the diagonal language. -/
theorem diag_eq_false {f : ℕ → ℕ} {x : List Bool} (hx : ∀ c : Code, codeCells c ≠ x) :
    diag f x = false := by
  have hd : decodeCodeCells x = none := by
    cases h : decodeCodeCells x with
    | none => rfl
    | some c => exact absurd (codeCells_of_decodeCodeCells_eq_some h) (hx c)
  simp only [diag, hd]

/-- **The diagonal language through the universal machine.** On the code stack of `c`, `diag f`
holds iff the clocked universal machine, which writes `encOut (c.evalSteps x T)` from
`encIn c x T` (`Clocked.nonempty_univPolyTime`), does not write the answer `true` from
`encIn c (codeCells c) (f |codeCells c|)`. -/
theorem diag_codeCells_eq_encOut (f : ℕ → ℕ) (c : Code) :
    diag f (codeCells c) = decide
      (encOut (c.evalSteps (codeCells c) (f (codeCells c).length)) ≠
        encOut (some [bitSym true])) := by
  rw [diag_codeCells]
  simp only [ne_eq, encOut_injective.eq_iff]

/-- **The diagonal argument** (from the proof of Sipser's Theorem 9.10): no code decides
`diag f` within `f` steps. A code `c` deciding it would, on its own code stack, answer the opposite
of `diag f`. -/
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

/-- **A hierarchy within codes, given an upper bound.** If `f ≤ g` and `diag f` is decided within
`g`, then `CodeTime f` is a proper subclass of `CodeTime g`. -/
theorem codeTime_ssubset_of_diag_mem {f g : ℕ → ℕ} (hfg : f ≤ g) (h : diag f ∈ CodeTime g) :
    CodeTime f ⊂ CodeTime g :=
  (Set.ssubset_iff_of_subset (codeTime_mono hfg)).2 ⟨diag f, h, diag_not_mem_codeTime f⟩

/-! ### The upper bound, up to the reformatting machine -/

/-- The universal machine's argument for `diag f` on `x`: the code encoded by `x`, the input `x`
and the clock `f |x|`; for a bit list that encodes no code, the code with no transitions on the
input `[true]`, which halts at once with the answer `true`, so that `diag f` reads `false`. -/
def diagArg (f : ℕ → ℕ) (x : List Bool) : Code × List Bool × ℕ :=
  match decodeCodeCells x with
  | some c => (c, x, f x.length)
  | none => (⟨[]⟩, [true], 0)

/-- **The reformatting function in bits.** The universal machine's input for `diag f` on `x` is
`cell (f |x|) ++ cells (input x) ++ false :: x.reverse` when `x` is a code stack, and a fixed
list otherwise. -/
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

/-- The answer of `diag` read from a clocked result: `true` unless the result is the answer
`true`. -/
def diagAnswer (o : Option (List ℕ)) : Bool := decide (o ≠ some [bitSym true])

/-- The answer read from the universal machine's output: `true` unless the output is
`encOut (some [bitSym true])`. -/
theorem diagAnswer_eq_decide_encOut (o : Option (List ℕ)) :
    diagAnswer o = decide (encOut o ≠ encOut (some [bitSym true])) := by
  simp only [diagAnswer, ne_eq, encOut_injective.eq_iff]

/-- **`diag f` through the universal function.** `diag f` is the answer read from the clocked
evaluator on `diagArg f`. -/
theorem diag_eq_comp (f : ℕ → ℕ) :
    diag f = diagAnswer ∘ (fun a : Code × List Bool × ℕ ↦ a.1.evalSteps a.2.1 a.2.2) ∘
      diagArg f := by
  funext x
  have h0 : Code.evalSteps ⟨[]⟩ [true] 0 = some [bitSym true] := by decide
  rcases hd : decodeCodeCells x with _ | c <;> simp [diag, diagArg, diagAnswer, hd, h0]

namespace Diag.Readout

open Function MetaMathlibExt.TM2Program

/-- The stacks of the readout machine: the input `X` and the output `O`. -/
inductive K | X | O
  deriving DecidableEq

/-- Finitely many stacks. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .O], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The labels: `r0` to `r3` read the bits of `encOut (some [bitSym true])`, `r4` checks that
nothing follows, `hit` and `miss` write the answer, `done` stops. -/
inductive Lab | r0 | r1 | r2 | r3 | r4 | hit | miss | done
  deriving DecidableEq

/-- Finitely many labels. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.r0, .r1, .r2, .r3, .r4, .hit, .miss, .done], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Every stack holds bits. -/
abbrev Γ : K → Type := fun _ => Bool

/-- Pop a bit of `X`; go to `next` if it is `b`, to `miss` otherwise. -/
def expect (b : Bool) (next : Lab) : TM2.Stmt Γ Lab Bool :=
  .pop .X (fun _ o ↦ o == some b) (.branch id (.goto fun _ ↦ next) (.goto fun _ ↦ .miss))

/-- The program: compare the input with `encOut (some [bitSym true]) = [true, true, true, false]`
and write `false` on a match, `true` otherwise. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .r0 => expect true .r1
  | .r1 => expect true .r2
  | .r2 => expect true .r3
  | .r3 => expect false .r4
  | .r4 => .pop .X (fun _ o ↦ o.isNone) (.branch id (.goto fun _ ↦ .hit) (.goto fun _ ↦ .miss))
  | .hit => .push .O (fun _ ↦ false) (.goto fun _ ↦ .done)
  | .miss => .push .O (fun _ ↦ true) (.goto fun _ ↦ .done)
  | .done => .halt

/-- The readout machine as a host component. -/
abbrev comp : Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ := fun _ ↦ inferInstanceAs (Fintype Bool)
  L := Lab
  prog := prog
  ks := [.X, .O]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **The readout run.** From the bits `l` on `X`, the machine stops at `done` within `6` steps
with the bit `l ≠ encOut (some [bitSym true])` on `O`. -/
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

/-- The readout machine on raw bits, in the reduction host. -/
noncomputable def bitsPolyTime :
    TM2ComputableInPolyTime (fun l : List Bool ↦ l) (fun l : List Bool ↦ l)
      (fun l ↦ [decide (l ≠ encOut (some [bitSym true]))]) :=
  Complexity.Host.reduction (c := comp) (cX := .X) (cO := .O) (gX := id) (start := .r0)
    (done := .done) (Equiv.refl Bool) _ (Polynomial.C 6) rfl fun l ↦ by
      obtain ⟨v, S', hr, hO⟩ := run l
      exact ⟨v, S', by simpa using hr, by simpa using hO⟩

/-- **The readout in polynomial time.** A `FinTM2` reads `encOut o` and writes the bit
`diagAnswer o`. -/
noncomputable def polyTime : TM2ComputableInPolyTime encOut (fun b : Bool ↦ [b]) diagAnswer where
  toTM2ComputableAux := bitsPolyTime.toTM2ComputableAux
  time := bitsPolyTime.time
  outputsFun o := by
    have h := bitsPolyTime.outputsFun (encOut o)
    rwa [← diagAnswer_eq_decide_encOut] at h

end Diag.Readout

/-- **The upper bound, given the reformatting machine.** If a `FinTM2` writes the universal
machine's input `encIn` of `diagArg f x` from the bits `x` in polynomial time, then a `FinTM2`
decides `diag f` in polynomial time: the reformatting machine, then the clocked universal machine
(`Clocked.nonempty_univPolyTime`), then the readout machine, composed by
`TM2Composition.compComputable`. -/
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
