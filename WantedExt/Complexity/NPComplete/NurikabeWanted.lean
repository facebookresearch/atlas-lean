/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NURIKABE is NP-complete

Source:
M. Holzer, A. Klein and M. Kutrib, "On the NP-completeness of the NURIKABE pencil puzzle and
variants thereof", Proceedings of the 3rd International Conference on Fun with Algorithms
(FUN 2004) (rules 1-4 and Theorem 1);
M. Holzer, A. Klein, M. Kutrib and O. Ruepp, "Computational complexity of NURIKABE",
Fundamenta Informaticae 110(1-4) (2011), 159-174, doi:10.3233/FI-2011-534;
first proved by B. McPhail, "The complexity of puzzles: NP-completeness results for Nurikabe
and Minesweeper", BA thesis, Reed College (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nurikabe

/-!
# NURIKABE is NP-complete

Nurikabe is played on a finite rectangular grid, some of whose cells are labelled with natural
numbers. The cells are filled black or white so that (Holzer, Klein and Kutrib 2004):
1. cells containing numbers are filled white;
2. a natural number defines a number of connected white cells (linked horizontally or
   vertically); each area of white cells contains only one natural number, and the areas are
   separated by black cells;
3. all black cells are linked to be a connected area;
4. black cells cannot be linked to form a `2 × 2` square.

INSTANCE: an `m × n` grid with some cells labelled by natural numbers.
QUESTION: can the cells be filled so that rules 1-4 hold?

The grid is given row by row: entry `c` of row `r` is `0` for an unlabelled cell and `k ≥ 1`
for a cell labelled `k`. `WellFormed` requires `m, n ≥ 1` and rows of equal length. A filling
is a function `ℕ → ℕ → Bool` (`true` = black) read on the grid. Cells are `Fin m × Fin n`,
linked horizontally or vertically when adjacent in Mathlib's grid graph
`pathGraph m □ pathGraph n`. An area of white cells is a connected component
(`SimpleGraph.ConnectedComponent`) of the subgraph the grid graph induces on the white cells;
rule 2 says each such area contains exactly one labelled cell and has as many cells as its
label. Rule 3 is `SimpleGraph.Preconnected` of the subgraph induced on the black cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid row by row, `0` for an unlabelled cell and `k ≥ 1` for label `k`. -/
abbrev NurikabeInstance := List (List ℕ)

/-- The number of rows. -/
def rows (i : NurikabeInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : NurikabeInstance) : ℕ := (i.headD []).length

/-- The label of cell `x` (`0` if unlabelled). -/
def label (i : NurikabeInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness: at least one row and one column, and rows of equal length. -/
def WellFormed (i : NurikabeInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ ∀ row ∈ i, row.length = cols i

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : NurikabeInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The filling `p` (`true` = black) satisfies rules 1-4. -/
def Solves (i : NurikabeInstance) (p : ℕ → ℕ → Bool) : Prop :=
  -- 1. cells containing numbers are white
  (∀ x : Fin (rows i) × Fin (cols i), label i x ≠ 0 → p x.1 x.2 = false) ∧
  -- 2. each white area contains exactly one number, equal to the number of its cells
  (∀ C : ((Grid i).induce {x | p x.1 x.2 = false}).ConnectedComponent,
    ∃ v ∈ C.supp, label i v.1 ≠ 0 ∧ (∀ w ∈ C.supp, label i w.1 ≠ 0 → w = v) ∧
      C.supp.ncard = label i v.1) ∧
  -- 3. the black cells form a connected area
  ((Grid i).induce {x | p x.1 x.2 = true}).Preconnected ∧
  -- 4. no `2 × 2` square of black cells
  ∀ r c, r + 1 < rows i → c + 1 < cols i →
    ¬ (p r c = true ∧ p r (c + 1) = true ∧ p (r + 1) c = true ∧ p (r + 1) (c + 1) = true)

/-- Some filling satisfies the rules. -/
def NurikabeFeasible (i : NurikabeInstance) : Prop :=
  ∃ p : ℕ → ℕ → Bool, Solves i p

open Classical in
/-- NURIKABE as a decision problem over bitstrings. -/
noncomputable def nurikabeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NurikabeInstance) x with
  | some i => decide (WellFormed i ∧ NurikabeFeasible i)
  | none => false

/-- **NURIKABE is NP-complete.** Source: Holzer, Klein and Kutrib (2004), Theorem 1; Holzer,
Klein, Kutrib and Ruepp (2011); McPhail (2003). -/
public theorem_wanted nurikabe_npComplete :
    nurikabeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nurikabeDec

end MetaMathlibExt.Complexity.NPComplete.Nurikabe
