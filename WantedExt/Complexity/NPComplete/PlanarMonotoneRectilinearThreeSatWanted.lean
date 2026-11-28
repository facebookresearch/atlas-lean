/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR MONOTONE RECTILINEAR 3SAT is NP-complete

Source:
M. de Berg and A. Khosravi, "Optimal binary space partitions in the plane", Computing and
Combinatorics (COCOON 2010), LNCS 6196 (2010), 216-225; journal version "Optimal binary space
partitions for segments in the plane", International Journal of Computational Geometry and
Applications 22(3) (2012), 187-205, doi:10.1142/S0218195912500045. Restated by A. Darmann,
J. Döcker and B. Dorn, arXiv:1604.05588 (2016), Section 1, and by A. K. Abu-Affash, P. Carmi and
J. S. B. Mitchell, arXiv:2607.06251 (2026), Section 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarMonotoneRectilinearThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarMonotoneRectilinearThreeSat

/-!
# PLANAR MONOTONE RECTILINEAR 3SAT is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of clauses over `U`, each with at most
three literals on distinct variables, every clause monotone (all of its literals positive, or
all negative), together with a monotone rectilinear representation of the variable-clause
incidence graph: the variables are drawn as axis-parallel rectangles along a horizontal line
`l`, the positive clauses as axis-parallel rectangles above `l`, the negative clauses as
axis-parallel rectangles below `l`, and each edge between a clause and a variable occurring in
it as a vertical segment, with no two of these objects crossing. QUESTION: is there a satisfying
truth assignment for `C`?

This is PLANAR 3SAT (`WantedExt.Complexity.NPComplete.PlanarThreeSatWanted`) restricted to
monotone formulas given with a monotone rectilinear representation; de Berg and Khosravi proved
it NP-complete. Darmann, Döcker and Dorn (Section 1): "The restriction of this problem [Planar
3-Sat, each clause containing at most three variables] ... to monotone instances remains
NP-complete, even if a rectilinear representation is given [dBK10]". Abu-Affash, Carmi and
Mitchell (Section 2) define the representation: "(i) the variables are drawn as axis-aligned
rectangles arranged along a horizontal line l, (ii) all positive clauses are drawn as
axis-aligned rectangles and lie on one side (above) of l, (iii) all negative clauses are drawn as
axis-aligned rectangles and lie on the other side (below) of l, and (iv) the edges connecting the
variables to the clauses are drawn as vertical segments". Some later restatements require
exactly three literals per clause; the at-most-three class stated here contains that class, so
it is NP-complete under either reading.

The formula uses the parent's encoding (`Cslib.Logic.LegacyPL.CNF`, variables `0, …, n - 1`, at most
three literals per clause) and the parent's `PlanarThreeSatFeasible`; the variables of a clause
are distinct, so that each variable-clause edge of the incidence graph has exactly one leg. The
representation is given with natural-number coordinates, the line `l` being the `x`-axis and the
rectangles shrunk to segments, which loses nothing for a finite drawing: variable `u` is the
interval `[aᵤ, bᵤ]` of `l`, the literal `j` of clause `c` is attached by the vertical leg at `x
= leg c j` running from `l` to height `h_c > 0` on the clause's side, and the clause is the
horizontal segment at height `h_c` between its leftmost and rightmost legs. The drawing is
crossing-free exactly when (`IsMonotoneRectilinearRepresentation`): the variable intervals are
disjoint, every leg lies in the interval of its variable, two legs on the same side have
different `x`, and no leg of a clause `c` meets the segment of another clause `c'` on the same
side with `h_{c'} ≤ h_c` (the leg runs from `l` up to height `h_c`, so it would cross or touch
that segment; at equal heights this also makes the two segments disjoint). Legs on opposite
sides only meet on `l`, inside their common variable.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR MONOTONE RECTILINEAR 3SAT is NP-complete.** Source: de Berg and Khosravi (2010,
2012). -/
public theorem_wanted planarMonotoneRectilinearThreeSat_npComplete :
    planarMonotoneRectilinearThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarMonotoneRectilinearThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.PlanarMonotoneRectilinearThreeSat
