/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.NeedlemanWunschTable
public import CSLibExt.Bioinformatics.Alignment.SmithWaterman

/-!
# Traceback for the Needleman–Wunsch and Smith–Waterman tables

The tables of `NeedlemanWunschTable` and `SmithWaterman` return scores only. Here every row is kept
(`nwTable`, `swTable`) and an alignment is read back by a traceback: from the current cell, step to
a neighbouring cell from which the recurrence attains the current value and emit the column. The
global traceback runs from the last cell to `(0, 0)`. The local one follows Smith and Waterman
(1981), who start at a largest cell and stop at a cell equal to `0`; it starts at the first largest
cell in row-major order (`argmaxCell`) and stops at the first cell equal to `0` that it reaches.
The paper fixes only that start and stop: the order among tied predecessors (diagonal, then up,
then left) and the choice of the first largest cell are this file's. Gaps are linear, as in
`SequenceAlignment`.

## Cost model

Let `m = |xs|` and `n = |ys|`. Building a table, converting it to an array of arrays, and, for the
local traceback, scanning it for its first largest cell each inspect all `(m + 1) (n + 1)` cells,
also when a sequence is empty, so each takes time `O((m + 1) (n + 1))`. The walk itself converts
the two sequences to arrays and then takes at most `m + n` steps, each reading its cells and
letters in constant time: time `O(m + n + 1)`.

## References

* S. B. Needleman and C. D. Wunsch, J. Mol. Biol. 48 (1970), 443–453.
* T. F. Smith and M. S. Waterman, J. Mol. Biol. 147 (1981), 195–197.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.Traceback

open Cslib.Algorithms.Lean

/-- **Table entry.** The entry `T[i][j]` of a table stored as an array of rows, read in constant
time; it is `0` outside the table. -/
def cell (T : Array (Array ℤ)) (i j : ℕ) : ℤ := (T.getD i #[]).getD j 0

/-- **Needleman–Wunsch table.** Every row `F[0], …, F[|xs|]` of the Needleman–Wunsch table of
`xs` and `ys`, row `0` being `F[0][j] = j * gap`. -/
def nwTable {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) : List (List ℤ) :=
  xs.scanl (fun row a => NeedlemanWunsch.nextRow σ gap a ys row)
    ((List.range (ys.length + 1)).map fun j : ℕ => gap * (j : ℤ))

/-- **Smith–Waterman table.** Every row `H[0], …, H[|xs|]` of the Smith–Waterman table of `xs`
and `ys`, row `0` being zero. -/
def swTable {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) : List (List ℤ) :=
  xs.scanl (fun row a => SmithWaterman.nextRow σ gap a ys row) (0 :: ys.map fun _ => 0)

/-- **Global traceback from a cell.** The global traceback from cell `(i, j)` of the table `T` with
fuel `n`, where `acc` holds the columns already emitted. A cell of the top row steps left and one
of the left column steps up; an interior cell steps diagonally if `T[i-1][j-1] + σ` gives the
cell, else up if `T[i-1][j] + gap` does, else left. It returns `acc` unchanged at cell `(0, 0)`,
when the fuel is `0` (at any cell), and when a letter it needs is missing (`i > |xs|` or
`j > |ys|`). `nwTraceback` starts at `(|xs|, |ys|)` with fuel `|xs| + |ys|`, and each step lowers
the fuel and `i + j` by one, so only `(0, 0)` stops it. The table and the sequences are arrays, so
a step reads its cells and letters in constant time. -/
def nwTraceAux {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (T : Array (Array ℤ)) (xs ys : Array α) :
    ℕ → ℕ → ℕ → Alignment α → Alignment α
  | 0, _, _, acc => acc
  | _ + 1, 0, 0, acc => acc
  | n + 1, i + 1, 0, acc =>
    match xs[i]? with
    | some a => nwTraceAux σ gap T xs ys n i 0 ((some a, none) :: acc)
    | none => acc
  | n + 1, 0, j + 1, acc =>
    match ys[j]? with
    | some b => nwTraceAux σ gap T xs ys n 0 j ((none, some b) :: acc)
    | none => acc
  | n + 1, i + 1, j + 1, acc =>
    match xs[i]?, ys[j]? with
    | some a, some b =>
      if cell T (i + 1) (j + 1) = cell T i j + σ a b then
        nwTraceAux σ gap T xs ys n i j ((some a, some b) :: acc)
      else if cell T (i + 1) (j + 1) = cell T i (j + 1) + gap then
        nwTraceAux σ gap T xs ys n i (j + 1) ((some a, none) :: acc)
      else
        nwTraceAux σ gap T xs ys n (i + 1) j ((none, some b) :: acc)
    | _, _ => acc

/-- **Needleman–Wunsch traceback.** The global alignment of `xs` and `ys` read back from the full
Needleman–Wunsch table, from cell `(|xs|, |ys|)` to cell `(0, 0)`, with the table and the
sequences converted to arrays once. -/
def nwTraceback {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) : Alignment α :=
  nwTraceAux σ gap ((nwTable σ gap xs ys).map List.toArray).toArray xs.toArray ys.toArray
    (xs.length + ys.length) xs.length ys.length []

/-- **First largest cell.** The position `(i, j)` of the first largest entry of a table in
row-major order (rows top to bottom, each row left to right): `List.argmax` of the entries
`((i, j), T[i][j])` listed in that order, which keeps the first of tied entries. It is `(0, 0)`
when the table has no entry. -/
def argmaxCell (T : List (List ℤ)) : ℕ × ℕ :=
  (((T.zipIdx.flatMap fun rowi => rowi.1.zipIdx.map fun vj => ((rowi.2, vj.2), vj.1)).argmax
    Prod.snd).map Prod.fst).getD (0, 0)

/-- **Local traceback from a cell.** The local traceback from cell `(i, j)` of the table `T` with
fuel `n`, where `acc` holds the columns already emitted. It stops at a cell of the top row or the
left column, at an interior cell equal to `0`, when the fuel is `0` (even at a nonzero interior
cell), and when a letter it needs is missing (`i > |xs|` or `j > |ys|`); it then returns that
cell's position and `acc`. Otherwise it steps as in `nwTraceAux`, in constant time per step.
`swTraceback` starts at a cell `(i, j)` of the table with fuel `i + j`, and each step lowers both
by one, so only the border or a cell equal to `0` stops it. -/
def swTraceAux {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (T : Array (Array ℤ)) (xs ys : Array α) :
    ℕ → ℕ → ℕ → Alignment α → ℕ × ℕ × Alignment α
  | 0, i, j, acc => (i, j, acc)
  | _ + 1, 0, j, acc => (0, j, acc)
  | _ + 1, i + 1, 0, acc => (i + 1, 0, acc)
  | n + 1, i + 1, j + 1, acc =>
    if cell T (i + 1) (j + 1) = 0 then (i + 1, j + 1, acc) else
    match xs[i]?, ys[j]? with
    | some a, some b =>
      if cell T (i + 1) (j + 1) = cell T i j + σ a b then
        swTraceAux σ gap T xs ys n i j ((some a, some b) :: acc)
      else if cell T (i + 1) (j + 1) = cell T i (j + 1) + gap then
        swTraceAux σ gap T xs ys n i (j + 1) ((some a, none) :: acc)
      else
        swTraceAux σ gap T xs ys n (i + 1) j ((none, some b) :: acc)
    | _, _ => (i + 1, j + 1, acc)

/-- **Local alignment with its bounds.** The output of a local traceback: the bounds of an infix
`(xs.take xEnd).drop xStart` of a first sequence `xs`, the bounds of an infix
`(ys.take yEnd).drop yStart` of a second sequence `ys`, and an alignment. The structure does not
constrain its fields; `swTraceback_spec` proves that `swTraceback` returns valid bounds and an
alignment of the two infixes. -/
structure LocalAlignment (α : Type*) where
  /-- The start of the infix of the first sequence. -/
  xStart : ℕ
  /-- The end of the infix of the first sequence, exclusive. -/
  xEnd : ℕ
  /-- The start of the infix of the second sequence. -/
  yStart : ℕ
  /-- The end of the infix of the second sequence, exclusive. -/
  yEnd : ℕ
  /-- The alignment of the two infixes. -/
  alignment : Alignment α
  deriving DecidableEq, Repr

/-- **Smith–Waterman traceback.** Start at the first largest cell `(i₁, j₁)` of the full
Smith–Waterman table of `xs` and `ys` and trace back to the first cell `(i₀, j₀)` equal to `0`.
The result is the alignment of the infixes `(xs.take i₁).drop i₀` and `(ys.take j₁).drop j₀`,
with `xStart = i₀`, `xEnd = i₁`, `yStart = j₀` and `yEnd = j₁`. The table and the sequences are
converted to arrays once. -/
def swTraceback {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) : LocalAlignment α :=
  let T := swTable σ gap xs ys
  let e := argmaxCell T
  let r := swTraceAux σ gap (T.map List.toArray).toArray xs.toArray ys.toArray
    (e.1 + e.2) e.1 e.2 []
  { xStart := r.1, xEnd := e.1, yStart := r.2.1, yEnd := e.2, alignment := r.2.2 }

private theorem scan_rows {α β : Type*} (f : List α → β) (step : β → α → β)
    (hstep : ∀ (px : List α) (a : α), step (f px) a = f (px ++ [a]))
    (xs pre : List α) :
    xs.scanl step (f pre) = xs.inits.map (fun q => f (pre ++ q)) := by
  induction xs generalizing pre with
  | nil => simp
  | cons a xs ih =>
    rw [List.scanl_cons, hstep, ih, List.inits_cons]
    simp [List.map_map, Function.comp_def, List.append_assoc]

/-- **Rows of the Needleman–Wunsch table.** Row `i` of the Needleman–Wunsch table is
`j ↦ nwScore (xs.take i) (ys.take j)`, for `i ≤ |xs|` and `j ≤ |ys|`. -/
theorem nwTable_eq {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) :
    nwTable σ gap xs ys = xs.inits.map fun px => ys.inits.map (nwScore σ gap px) := by
  have hrow :
      (List.range (ys.length + 1)).map (fun j : ℕ => gap * (j : ℤ)) =
        ys.inits.map (nwScore σ gap []) := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      have hj : j ≤ ys.length := by simp at h1; omega
      rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_inits,
        nwScore_nil_left, List.length_take, Nat.min_eq_left hj]
  rw [nwTable, hrow]
  simpa using scan_rows (fun px => ys.inits.map (nwScore σ gap px))
    (fun row a => NeedlemanWunsch.nextRow σ gap a ys row)
    (fun px a => NeedlemanWunsch.nextRow_eq σ gap a px ys) xs []

/-- **Rows of the Smith–Waterman table.** Row `i` of the Smith–Waterman table is
`j ↦ swCellScore (xs.take i) (ys.take j)`, for `i ≤ |xs|` and `j ≤ |ys|`. -/
theorem swTable_eq {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) :
    swTable σ gap xs ys = xs.inits.map fun px => ys.inits.map (swCellScore σ gap px) := by
  have hrow : (0 :: ys.map fun _ => (0 : ℤ)) =
      ys.inits.map (swCellScore σ gap []) := by
    rw [List.map_congr_left fun py _ => swCellScore_nil_left σ gap py]
    induction ys with
    | nil => rfl
    | cons b ys ih => simp [List.map_map, Function.comp_def, ← ih]
  rw [swTable, hrow]
  simpa using scan_rows (fun px => ys.inits.map (swCellScore σ gap px))
    (fun row a => SmithWaterman.nextRow σ gap a ys row)
    (fun px a => SmithWaterman.nextRow_eq σ gap a px ys) xs []

/-- A table stored as a list of rows, as the array of rows that the tracebacks read. -/
private def tab (T : List (List ℤ)) : Array (Array ℤ) := (T.map List.toArray).toArray

private theorem cell_get (T : List (List ℤ)) (i j : ℕ)
    (hi : i < T.length) (hj : j < T[i].length) : cell (tab T) i j = T[i][j] := by
  simp [cell, tab, hi, hj]

private theorem cell_prefix {α : Type*} (f : List α → List α → ℤ)
    (xs ys : List α) (i j : ℕ) (hi : i ≤ xs.length) (hj : j ≤ ys.length) :
    cell (tab (xs.inits.map fun px => ys.inits.map (f px))) i j =
      f (xs.take i) (ys.take j) := by
  rw [cell_get _ i j (by simp; omega) (by simp; omega)]
  simp

private theorem cell_nw {α : Type*} (σ : α → α → ℤ) (gap : ℤ)
    (xs ys : List α) (i j : ℕ) (hi : i ≤ xs.length) (hj : j ≤ ys.length) :
    cell (tab (nwTable σ gap xs ys)) i j = nwScore σ gap (xs.take i) (ys.take j) := by
  rw [nwTable_eq]
  exact cell_prefix (nwScore σ gap) xs ys i j hi hj

private theorem cell_sw {α : Type*} (σ : α → α → ℤ) (gap : ℤ)
    (xs ys : List α) (i j : ℕ) (hi : i ≤ xs.length) (hj : j ≤ ys.length) :
    cell (tab (swTable σ gap xs ys)) i j = swCellScore σ gap (xs.take i) (ys.take j) := by
  rw [swTable_eq]
  exact cell_prefix (swCellScore σ gap) xs ys i j hi hj

private theorem drop_step {α : Type*} (xs : List α) (e i : ℕ)
    (he : e ≤ xs.length) (hi : i < e) :
    (xs.take e).drop i = xs[i]'(by omega) :: (xs.take e).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_take]

private theorem cons_alignment {α : Type*} (a b : Option α)
    (A : Alignment α) (xs ys : List α) (hc : (a, b) ≠ (none, none))
    (hA : IsAlignment A xs ys) :
    IsAlignment ((a, b) :: A) (a.toList ++ xs) (b.toList ++ ys) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c h
    rcases List.mem_cons.mp h with rfl | h
    · exact hc
    · exact hA.1 c h
  · cases a <;> simpa using hA.2.1
  · cases b <;> simpa using hA.2.2

private theorem nw_step {α : Type*} (σ : α → α → ℤ) (gap : ℤ)
    (xs ys : List α) (i j : ℕ) (hi : i < xs.length) (hj : j < ys.length) :
    cell (tab (nwTable σ gap xs ys)) (i + 1) (j + 1) =
      max (max (cell (tab (nwTable σ gap xs ys)) i j + σ xs[i] ys[j])
        (cell (tab (nwTable σ gap xs ys)) i (j + 1) + gap))
        (cell (tab (nwTable σ gap xs ys)) (i + 1) j + gap) := by
  rw [cell_nw σ gap xs ys (i + 1) (j + 1) (by omega) (by omega),
    cell_nw σ gap xs ys i j (by omega) (by omega),
    cell_nw σ gap xs ys i (j + 1) (by omega) (by omega),
    cell_nw σ gap xs ys (i + 1) j (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hi, List.take_succ_eq_append_getElem hj,
    nwScore_snoc]

private theorem nw_worker {α : Type*} (σ : α → α → ℤ) (gap : ℤ)
    (xs ys : List α) (e f : ℕ) (he : e ≤ xs.length) (hf : f ≤ ys.length)
    (n i j : ℕ) (hi : i ≤ e) (hj : j ≤ f) (hn : i + j ≤ n)
    (acc : Alignment α) (hacc : IsAlignment acc ((xs.take e).drop i)
      ((ys.take f).drop j)) :
    IsAlignment (nwTraceAux σ gap (tab (nwTable σ gap xs ys)) xs.toArray ys.toArray n i j acc)
      (xs.take e) (ys.take f) ∧
      alignmentScore σ gap
        (nwTraceAux σ gap (tab (nwTable σ gap xs ys)) xs.toArray ys.toArray n i j acc) =
        cell (tab (nwTable σ gap xs ys)) i j + alignmentScore σ gap acc := by
  induction n generalizing i j acc with
  | zero =>
    have h0 : i = 0 ∧ j = 0 := by omega
    rcases h0 with ⟨rfl, rfl⟩
    constructor
    · simpa [nwTraceAux] using hacc
    · simp [nwTraceAux, cell_nw σ gap xs ys 0 0 (by omega) (by omega),
        nwScore_nil_left]
  | succ n ih =>
    cases i with
    | zero =>
      cases j with
      | zero =>
        constructor
        · simpa [nwTraceAux] using hacc
        · simp [nwTraceAux, cell_nw σ gap xs ys 0 0 (by omega) (by omega),
            nwScore_nil_left]
      | succ j =>
        have hb : j < ys.length := by omega
        have ha : IsAlignment ((none, some ys[j]) :: acc)
            ((xs.take e).drop 0) ((ys.take f).drop j) := by
          rw [drop_step ys f j hf (by omega)]
          simpa using cons_alignment none (some ys[j]) acc _ _ (by simp) hacc
        have hs : cell (tab (nwTable σ gap xs ys)) 0 (j + 1) =
            cell (tab (nwTable σ gap xs ys)) 0 j + gap := by
          rw [cell_nw σ gap xs ys 0 (j + 1) (by omega) (by omega),
            cell_nw σ gap xs ys 0 j (by omega) (by omega)]
          simp [nwScore_nil_left, List.length_take, Nat.min_eq_left (by omega : j ≤ ys.length),
            Nat.min_eq_left (by omega : j + 1 ≤ ys.length)]
          ring
        simp only [nwTraceAux, List.getElem?_toArray, List.getElem?_eq_getElem hb]
        obtain ⟨hA, hS⟩ := ih 0 j (by omega) (by omega) (by omega) _ ha
        refine ⟨hA, ?_⟩
        rw [hS, hs]
        simp [alignmentScore, columnScore]
        omega
    | succ i =>
      have hx : i < xs.length := by omega
      cases j with
      | zero =>
        have ha : IsAlignment ((some xs[i], none) :: acc)
            ((xs.take e).drop i) ((ys.take f).drop 0) := by
          rw [drop_step xs e i he (by omega)]
          simpa using cons_alignment (some xs[i]) none acc _ _ (by simp) hacc
        have hs : cell (tab (nwTable σ gap xs ys)) (i + 1) 0 =
            cell (tab (nwTable σ gap xs ys)) i 0 + gap := by
          rw [cell_nw σ gap xs ys (i + 1) 0 (by omega) (by omega),
            cell_nw σ gap xs ys i 0 (by omega) (by omega)]
          simp [nwScore_nil_right, List.length_take, Nat.min_eq_left (by omega : i ≤ xs.length),
            Nat.min_eq_left (by omega : i + 1 ≤ xs.length)]
          ring
        simp only [nwTraceAux, List.getElem?_toArray, List.getElem?_eq_getElem hx]
        obtain ⟨hA, hS⟩ := ih i 0 (by omega) (by omega) (by omega) _ ha
        refine ⟨hA, ?_⟩
        rw [hS, hs]
        simp [alignmentScore, columnScore]
        omega
      | succ j =>
        have hy : j < ys.length := by omega
        have hd : IsAlignment ((some xs[i], some ys[j]) :: acc)
            ((xs.take e).drop i) ((ys.take f).drop j) := by
          rw [drop_step xs e i he (by omega), drop_step ys f j hf (by omega)]
          simpa using cons_alignment (some xs[i]) (some ys[j]) acc _ _ (by simp) hacc
        have hu : IsAlignment ((some xs[i], none) :: acc)
            ((xs.take e).drop i) ((ys.take f).drop (j + 1)) := by
          rw [drop_step xs e i he (by omega)]
          simpa using cons_alignment (some xs[i]) none acc _ _ (by simp) hacc
        have hl : IsAlignment ((none, some ys[j]) :: acc)
            ((xs.take e).drop (i + 1)) ((ys.take f).drop j) := by
          rw [drop_step ys f j hf (by omega)]
          simpa using cons_alignment none (some ys[j]) acc _ _ (by simp) hacc
        simp only [nwTraceAux, List.getElem?_toArray, List.getElem?_eq_getElem hx,
          List.getElem?_eq_getElem hy]
        split
        · rename_i hs
          obtain ⟨hA, hS⟩ := ih i j (by omega) (by omega) (by omega) _ hd
          refine ⟨hA, ?_⟩
          rw [hS, hs]
          simp [alignmentScore, columnScore]
          omega
        · rename_i hnd
          split
          · rename_i hs
            obtain ⟨hA, hS⟩ := ih i (j + 1) (by omega) (by omega) (by omega) _ hu
            refine ⟨hA, ?_⟩
            rw [hS, hs]
            simp [alignmentScore, columnScore]
            omega
          · rename_i hnu
            have hs : cell (tab (nwTable σ gap xs ys)) (i + 1) (j + 1) =
                cell (tab (nwTable σ gap xs ys)) (i + 1) j + gap := by
              have h := nw_step σ gap xs ys i j hx hy
              simp only [max_def] at h
              split at h <;> split at h <;> omega
            obtain ⟨hA, hS⟩ := ih (i + 1) j (by omega) (by omega) (by omega) _ hl
            refine ⟨hA, ?_⟩
            rw [hS, hs]
            simp [alignmentScore, columnScore]
            omega

/-- **The global traceback is an alignment.** The Needleman–Wunsch traceback is an alignment of
`xs` and `ys`. -/
theorem isAlignment_nwTraceback {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) :
    IsAlignment (nwTraceback σ gap xs ys) xs ys := by
  have h := nw_worker σ gap xs ys xs.length ys.length le_rfl le_rfl
    (xs.length + ys.length) xs.length ys.length le_rfl le_rfl le_rfl []
    (by simp [IsAlignment])
  simpa [nwTraceback, tab] using h.1

/-- **The global traceback attains the table value.** For every `σ` and `gap`, the
Needleman–Wunsch traceback scores `nwTab`, the last cell of the table. -/
theorem alignmentScore_nwTraceback {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) :
    alignmentScore σ gap (nwTraceback σ gap xs ys) = NeedlemanWunsch.nwTab σ gap xs ys := by
  have h := nw_worker σ gap xs ys xs.length ys.length le_rfl le_rfl
    (xs.length + ys.length) xs.length ys.length le_rfl le_rfl le_rfl []
    (by simp [IsAlignment])
  rw [cell_nw σ gap xs ys xs.length ys.length le_rfl le_rfl] at h
  rw [NeedlemanWunsch.nwTab_eq_nwScore]
  simpa [nwTraceback, tab, alignmentScore_nil] using h.2

/-- **The global traceback is an optimal global alignment.** For every `σ` and `gap`, no alignment
of `xs` and `ys` scores more than the Needleman–Wunsch traceback. -/
theorem alignmentScore_le_nwTraceback {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α)
    (A : Alignment α) (hA : IsAlignment A xs ys) :
    alignmentScore σ gap A ≤ alignmentScore σ gap (nwTraceback σ gap xs ys) := by
  rw [alignmentScore_nwTraceback, NeedlemanWunsch.nwTab_eq_nwScore]
  exact alignmentScore_le_nwScore σ gap xs ys A hA

private theorem sw_step {α : Type*} (σ : α → α → ℤ) (gap : ℤ)
    (xs ys : List α) (i j : ℕ) (hi : i < xs.length) (hj : j < ys.length) :
    cell (tab (swTable σ gap xs ys)) (i + 1) (j + 1) =
      max 0 (max (max (cell (tab (swTable σ gap xs ys)) i j + σ xs[i] ys[j])
        (cell (tab (swTable σ gap xs ys)) i (j + 1) + gap))
        (cell (tab (swTable σ gap xs ys)) (i + 1) j + gap)) := by
  rw [cell_sw σ gap xs ys (i + 1) (j + 1) (by omega) (by omega),
    cell_sw σ gap xs ys i j (by omega) (by omega),
    cell_sw σ gap xs ys i (j + 1) (by omega) (by omega),
    cell_sw σ gap xs ys (i + 1) j (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hi, List.take_succ_eq_append_getElem hj,
    swCellScore_eq]

private theorem sw_worker {α : Type*} (σ : α → α → ℤ) (gap : ℤ)
    (xs ys : List α) (e f : ℕ) (he : e ≤ xs.length) (hf : f ≤ ys.length)
    (n i j : ℕ) (hi : i ≤ e) (hj : j ≤ f) (hn : i + j ≤ n)
    (acc : Alignment α) (hacc : IsAlignment acc ((xs.take e).drop i)
      ((ys.take f).drop j)) :
    let r := swTraceAux σ gap (tab (swTable σ gap xs ys)) xs.toArray ys.toArray n i j acc
    r.1 ≤ i ∧ r.2.1 ≤ j ∧
      IsAlignment r.2.2 ((xs.take e).drop r.1) ((ys.take f).drop r.2.1) ∧
      alignmentScore σ gap r.2.2 =
        cell (tab (swTable σ gap xs ys)) i j + alignmentScore σ gap acc := by
  induction n generalizing i j acc with
  | zero =>
    have h0 : i = 0 ∧ j = 0 := by omega
    rcases h0 with ⟨rfl, rfl⟩
    simp only [swTraceAux]
    refine ⟨le_rfl, le_rfl, hacc, ?_⟩
    simp [cell_sw σ gap xs ys 0 0 (by omega) (by omega), swCellScore_nil_left]
  | succ n ih =>
    cases i with
    | zero =>
      cases j with
      | zero =>
        simp only [swTraceAux]
        refine ⟨le_rfl, le_rfl, hacc, ?_⟩
        simp [cell_sw σ gap xs ys 0 0 (by omega) (by omega), swCellScore_nil_left]
      | succ j =>
        simp only [swTraceAux]
        refine ⟨le_rfl, le_rfl, hacc, ?_⟩
        simp [cell_sw σ gap xs ys 0 (j + 1) (by omega) (by omega), swCellScore_nil_left]
    | succ i =>
      have hx : i < xs.length := by omega
      cases j with
      | zero =>
        simp only [swTraceAux]
        refine ⟨le_rfl, le_rfl, hacc, ?_⟩
        simp [cell_sw σ gap xs ys (i + 1) 0 (by omega) (by omega), swCellScore_nil_right]
      | succ j =>
        have hy : j < ys.length := by omega
        have hd : IsAlignment ((some xs[i], some ys[j]) :: acc)
            ((xs.take e).drop i) ((ys.take f).drop j) := by
          rw [drop_step xs e i he (by omega), drop_step ys f j hf (by omega)]
          simpa using cons_alignment (some xs[i]) (some ys[j]) acc _ _ (by simp) hacc
        have hu : IsAlignment ((some xs[i], none) :: acc)
            ((xs.take e).drop i) ((ys.take f).drop (j + 1)) := by
          rw [drop_step xs e i he (by omega)]
          simpa using cons_alignment (some xs[i]) none acc _ _ (by simp) hacc
        have hl : IsAlignment ((none, some ys[j]) :: acc)
            ((xs.take e).drop (i + 1)) ((ys.take f).drop j) := by
          rw [drop_step ys f j hf (by omega)]
          simpa using cons_alignment none (some ys[j]) acc _ _ (by simp) hacc
        by_cases hz : cell (tab (swTable σ gap xs ys)) (i + 1) (j + 1) = 0
        · simp only [swTraceAux, ite_eq_left hz]
          refine ⟨le_rfl, le_rfl, hacc, ?_⟩
          rw [hz, zero_add]
        · simp only [swTraceAux, ite_eq_right hz, List.getElem?_toArray,
            List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy]
          split
          · rename_i hs
            obtain ⟨hri, hrj, hA, hS⟩ := ih i j (by omega) (by omega) (by omega) _ hd
            refine ⟨by omega, by omega, hA, ?_⟩
            rw [hS, hs]
            simp [alignmentScore, columnScore]
            omega
          · rename_i hnd
            split
            · rename_i hs
              obtain ⟨hri, hrj, hA, hS⟩ := ih i (j + 1) (by omega) (by omega) (by omega) _ hu
              refine ⟨by omega, by omega, hA, ?_⟩
              rw [hS, hs]
              simp [alignmentScore, columnScore]
              omega
            · rename_i hnu
              have hs : cell (tab (swTable σ gap xs ys)) (i + 1) (j + 1) =
                  cell (tab (swTable σ gap xs ys)) (i + 1) j + gap := by
                have h := sw_step σ gap xs ys i j hx hy
                simp only [max_def] at h
                split at h <;> split at h <;> split at h <;> omega
              obtain ⟨hri, hrj, hA, hS⟩ := ih (i + 1) j (by omega) (by omega) (by omega) _ hl
              refine ⟨by omega, by omega, hA, ?_⟩
              rw [hS, hs]
              simp [alignmentScore, columnScore]
              omega

private theorem mem_entries (T : List (List ℤ)) (i j : ℕ) (v : ℤ) :
    ((i, j), v) ∈
        T.zipIdx.flatMap (fun rowi => rowi.1.zipIdx.map fun vj => ((rowi.2, vj.2), vj.1)) ↔
      ∃ (hi : i < T.length) (hj : j < T[i].length), v = T[i][j] := by
  constructor
  · intro hc
    obtain ⟨⟨row, i'⟩, hrowi, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨v', j'⟩, hvj, he⟩ := List.mem_map.mp hc
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    have hrow := List.mem_zipIdx_iff_getElem?.mp hrowi
    have hv := List.mem_zipIdx_iff_getElem?.mp hvj
    dsimp only at hrow hv
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hrow
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    exact ⟨hi, hj, rfl⟩
  · rintro ⟨hi, hj, rfl⟩
    refine List.mem_flatMap.mpr ⟨(T[i], i), ?_, List.mem_map.mpr ⟨(T[i][j], j), ?_, rfl⟩⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
    · exact List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hj)

private theorem argmax_spec (T : List (List ℤ)) (m n : ℕ)
    (hrows : T.length = m + 1) (hcols : ∀ row ∈ T, row.length = n + 1) :
    (argmaxCell T).1 ≤ m ∧ (argmaxCell T).2 ≤ n ∧
      ∀ i j, i ≤ m → j ≤ n →
        cell (tab T) i j ≤ cell (tab T) (argmaxCell T).1 (argmaxCell T).2 := by
  let E := T.zipIdx.flatMap fun rowi => rowi.1.zipIdx.map fun vj => ((rowi.2, vj.2), vj.1)
  have hlen : ∀ i (hi : i < T.length), T[i].length = n + 1 := fun i hi =>
    hcols T[i] (List.getElem_mem hi)
  have h0 : ((0, 0), T[0][0]'(by rw [hlen 0 (by omega)]; omega)) ∈ E :=
    (mem_entries T 0 0 _).2 ⟨by omega, by rw [hlen 0 (by omega)]; omega, rfl⟩
  obtain ⟨⟨⟨i₀, j₀⟩, v₀⟩, hr⟩ : ∃ r, E.argmax Prod.snd = some r := by
    cases h : E.argmax Prod.snd with
    | none =>
      rw [List.argmax_eq_none] at h
      rw [h] at h0
      cases h0
    | some r => exact ⟨r, rfl⟩
  obtain ⟨hi, hj, hv⟩ := (mem_entries T i₀ j₀ v₀).1 (List.argmax_mem (Option.mem_def.2 hr))
  have he : argmaxCell T = (i₀, j₀) := by
    change ((E.argmax Prod.snd).map Prod.fst).getD (0, 0) = (i₀, j₀)
    rw [hr]
    rfl
  rw [he]
  have hjn := hlen i₀ hi
  refine ⟨show i₀ ≤ m by omega, show j₀ ≤ n by omega, ?_⟩
  intro i j hi' hj'
  have hir : i < T.length := by omega
  have hjr : j < T[i].length := by rw [hlen i hir]; omega
  rw [cell_get T i j hir hjr, cell_get T i₀ j₀ hi hj, ← hv]
  exact List.le_of_mem_argmax (f := Prod.snd) ((mem_entries T i j _).2 ⟨hir, hjr, rfl⟩)
    (Option.mem_def.2 hr)

private theorem sw_maximum {α : Type*} (σ : α → α → ℤ) (gap : ℤ)
    (xs ys : List α) :
    let e := argmaxCell (swTable σ gap xs ys)
    e.1 ≤ xs.length ∧ e.2 ≤ ys.length ∧
      cell (tab (swTable σ gap xs ys)) e.1 e.2 = SmithWaterman.swTab σ gap xs ys := by
  have hrows : (swTable σ gap xs ys).length = xs.length + 1 := by
    simp [swTable_eq]
  have hcols : ∀ row ∈ swTable σ gap xs ys, row.length = ys.length + 1 := by
    rw [swTable_eq]
    intro row hrow
    obtain ⟨px, -, rfl⟩ := List.mem_map.mp hrow
    simp
  obtain ⟨hi, hj, hmax⟩ := argmax_spec (swTable σ gap xs ys) xs.length ys.length hrows hcols
  refine ⟨hi, hj, ?_⟩
  rw [SmithWaterman.swTab_eq_swScore]
  apply le_antisymm
  · rw [cell_sw σ gap xs ys _ _ hi hj]
    exact swCellScore_le_swScore σ gap
      (mem_prefixPairs.mpr ⟨List.take_prefix _ _, List.take_prefix _ _⟩)
  · apply swScore_le σ gap
    intro p hp
    rw [mem_prefixPairs] at hp
    have h := hmax p.1.length p.2.length hp.1.length_le hp.2.length_le
    rw [cell_sw σ gap xs ys _ _ hp.1.length_le hp.2.length_le,
      ← List.prefix_iff_eq_take.mp hp.1, ← List.prefix_iff_eq_take.mp hp.2] at h
    exact h

/-- **Bounds, validity and score of the local traceback.** For every `σ` and `gap`, the
Smith–Waterman traceback returns bounds `xStart ≤ xEnd ≤ |xs|` and `yStart ≤ yEnd ≤ |ys|` and an
alignment of the infixes `(xs.take xEnd).drop xStart` and `(ys.take yEnd).drop yStart` that scores
`swTab`, the largest cell of the table. -/
theorem swTraceback_spec {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) :
    (swTraceback σ gap xs ys).xStart ≤ (swTraceback σ gap xs ys).xEnd ∧
      (swTraceback σ gap xs ys).xEnd ≤ xs.length ∧
      (swTraceback σ gap xs ys).yStart ≤ (swTraceback σ gap xs ys).yEnd ∧
      (swTraceback σ gap xs ys).yEnd ≤ ys.length ∧
      IsAlignment (swTraceback σ gap xs ys).alignment
        ((xs.take (swTraceback σ gap xs ys).xEnd).drop (swTraceback σ gap xs ys).xStart)
        ((ys.take (swTraceback σ gap xs ys).yEnd).drop (swTraceback σ gap xs ys).yStart) ∧
      alignmentScore σ gap (swTraceback σ gap xs ys).alignment =
        SmithWaterman.swTab σ gap xs ys := by
  let e := argmaxCell (swTable σ gap xs ys)
  have hm := sw_maximum σ gap xs ys
  have hw := sw_worker σ gap xs ys e.1 e.2 hm.1 hm.2.1
    (e.1 + e.2) e.1 e.2 le_rfl le_rfl le_rfl [] (by simp [IsAlignment])
  change _ ≤ e.1 ∧ e.1 ≤ xs.length ∧ _ ≤ e.2 ∧ e.2 ≤ ys.length ∧ _
  refine ⟨hw.1, hm.1, hw.2.1, hm.2.1, hw.2.2.1, ?_⟩
  have hs := hw.2.2.2
  simp only [e, hm.2.2, alignmentScore_nil, add_zero] at hs
  simpa [swTraceback, e, tab] using hs

/-- **The local traceback is an optimal local alignment.** For `gap ≤ 0`, no alignment of any pair
of infixes of `xs` and `ys` scores more than the alignment that `swTraceback` returns. -/
theorem alignmentScore_le_swTraceback {α : Type*} (σ : α → α → ℤ) (gap : ℤ) (hgap : gap ≤ 0)
    (xs ys xs' ys' : List α) (hx : xs' <:+: xs) (hy : ys' <:+: ys) (A : Alignment α)
    (hA : IsAlignment A xs' ys') :
    alignmentScore σ gap A ≤ alignmentScore σ gap (swTraceback σ gap xs ys).alignment := by
  obtain ⟨px, hxs, hpx⟩ := List.infix_iff_suffix_prefix.mp hx
  obtain ⟨py, hys, hpy⟩ := List.infix_iff_suffix_prefix.mp hy
  have hmem : (xs', ys') ∈ infixPairs xs ys :=
    mem_infixPairs.mpr ⟨px, py, hpx, hpy, hxs, hys⟩
  rw [(swTraceback_spec σ gap xs ys).2.2.2.2.2,
    SmithWaterman.swTab_eq_localScore σ gap hgap]
  exact le_trans (alignmentScore_le_nwScore σ gap xs' ys' A hA)
    (nwScore_le_localScore σ gap hmem)

end Cslib.Bioinformatics.Alignment.Traceback
