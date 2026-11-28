/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR MONOTONE RECTILINEAR 3SAT: definitions

Source:
M. de Berg and A. Khosravi, "Optimal binary space partitions in the plane", Computing and
Combinatorics (COCOON 2010), LNCS 6196 (2010), 216-225; journal version "Optimal binary space
partitions for segments in the plane", International Journal of Computational Geometry and
Applications 22(3) (2012), 187-205, doi:10.1142/S0218195912500045. Restated by A. Darmann,
J. Döcker and B. Dorn, arXiv:1604.05588 (2016), Section 1, and by A. K. Abu-Affash, P. Carmi and
J. S. B. Mitchell, arXiv:2607.06251 (2026), Section 2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PlanarThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarMonotoneRectilinearThreeSat

/-- An instance: the number `n` of variables, the CNF formula (a list of clauses, each a list
of literals `(variable, polarity)`), the variable intervals `[aᵤ, bᵤ]`, the clause heights
`h_c`, and for each clause the `x`-coordinates of its legs, one per literal. -/
abbrev PlanarMonotoneRectilinearThreeSatInstance :=
  ℕ × Cslib.Logic.LegacyPL.CNF × List (ℕ × ℕ) × List ℕ × List (List ℕ)

/-- The clause `c` of the formula. -/
def clause (i : PlanarMonotoneRectilinearThreeSatInstance) (c : ℕ) :
    Cslib.Logic.LegacyPL.CNFClause :=
  i.2.1.getD c []

/-- The side of clause `c`: `true` (above `l`) for a positive clause, `false` (below `l`) for a
negative one, read off its first literal. -/
def side (i : PlanarMonotoneRectilinearThreeSatInstance) (c : ℕ) : Bool :=
  ((clause i c).headD (0, true)).2

/-- The interval `[aᵤ, bᵤ]` of variable `u` on the line `l`. -/
def varInterval (i : PlanarMonotoneRectilinearThreeSatInstance) (u : ℕ) : ℕ × ℕ :=
  i.2.2.1.getD u (0, 0)

/-- The height `h_c` of clause `c` above (or below) the line `l`. -/
def height (i : PlanarMonotoneRectilinearThreeSatInstance) (c : ℕ) : ℕ :=
  i.2.2.2.1.getD c 0

/-- The `x`-coordinate of the leg of literal `j` of clause `c`. -/
def leg (i : PlanarMonotoneRectilinearThreeSatInstance) (c j : ℕ) : ℕ :=
  (i.2.2.2.2.getD c []).getD j 0

/-- The data form a crossing-free monotone rectilinear representation: one interval per
variable, one height and one leg per literal for each clause; the intervals are disjoint; the
heights are positive; each leg lies in the interval of its literal's variable; legs on the same
side have different `x`; and no leg of a clause `c` lies in the `x`-range of the segment of a
different clause `c'` on the same side with `h_{c'} ≤ h_c`. -/
def IsMonotoneRectilinearRepresentation (i : PlanarMonotoneRectilinearThreeSatInstance) : Prop :=
  i.2.2.1.length = i.1 ∧ i.2.2.2.1.length = i.2.1.length ∧
    i.2.2.2.2.map List.length = i.2.1.map List.length ∧
    (∀ u < i.1, (varInterval i u).1 ≤ (varInterval i u).2) ∧
    (∀ u < i.1, ∀ v < i.1, u ≠ v →
      (varInterval i u).2 < (varInterval i v).1 ∨ (varInterval i v).2 < (varInterval i u).1) ∧
    (∀ h ∈ i.2.2.2.1, 0 < h) ∧
    (∀ c < i.2.1.length, ∀ j < (clause i c).length,
      (varInterval i ((clause i c).getD j (0, true)).1).1 ≤ leg i c j ∧
        leg i c j ≤ (varInterval i ((clause i c).getD j (0, true)).1).2) ∧
    (∀ c < i.2.1.length, ∀ c' < i.2.1.length, side i c = side i c' →
      ∀ j < (clause i c).length, ∀ j' < (clause i c').length,
        (c, j) ≠ (c', j') → leg i c j ≠ leg i c' j') ∧
    (∀ c < i.2.1.length, ∀ c' < i.2.1.length, c ≠ c' → side i c = side i c' →
      height i c' ≤ height i c → ∀ j < (clause i c).length,
        ∀ j₁ < (clause i c').length, ∀ j₂ < (clause i c').length,
          ¬ (leg i c' j₁ ≤ leg i c j ∧ leg i c j ≤ leg i c' j₂))

/-- Well-formedness of an instance: every clause has at most three literals, on distinct
variables among `0, …, n - 1`, every clause is monotone, and the representation is a crossing-free
monotone rectilinear representation. -/
def WellFormed (i : PlanarMonotoneRectilinearThreeSatInstance) : Prop :=
  (∀ C ∈ i.2.1, C.length ≤ 3 ∧ (C.map Prod.fst).Nodup ∧ ∀ l ∈ C, l.1 < i.1) ∧
    (∀ C ∈ i.2.1, (∀ l ∈ C, l.2 = true) ∨ ∀ l ∈ C, l.2 = false) ∧
    IsMonotoneRectilinearRepresentation i

/-- Some truth assignment to the `n` variables satisfies every clause (the parent's
`PlanarThreeSatFeasible` on the formula). -/
def PlanarMonotoneRectilinearThreeSatFeasible
    (i : PlanarMonotoneRectilinearThreeSatInstance) : Prop :=
  PlanarThreeSat.PlanarThreeSatFeasible (i.1, i.2.1)

open Classical in
/-- PLANAR MONOTONE RECTILINEAR 3SAT as a decision problem over bitstrings. -/
noncomputable def planarMonotoneRectilinearThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarMonotoneRectilinearThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ PlanarMonotoneRectilinearThreeSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarMonotoneRectilinearThreeSat
