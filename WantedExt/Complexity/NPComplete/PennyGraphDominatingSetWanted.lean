/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET IN PENNY GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET;
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics 86
(1990), 165-177, doi:10.1016/0012-365X(90)90358-O (DOMINATING SET on unit disk graphs and on
grid graphs);
M. de Berg, H. L. Bodlaender, S. Kisfaludi-Bak, D. Marx and T. C. van der Zanden, "A framework
for exponential-time-hypothesis-tight algorithms and lower bounds in geometric intersection
graphs", SIAM Journal on Computing 49 (2020), 1291-1331, doi:10.1137/20M1320870,
arXiv:1803.10633, Theorem 32 (a reduction from 3-SAT to DOMINATING SET on induced grid graphs);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1381` (penny),
problem Domination: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitDiskDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PennyGraphDominatingSet

open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet
open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (point)

/-!
# DOMINATING SET IN PENNY GRAPHS is NP-complete

INSTANCE: a finite set `P` of points in the plane with rational coordinates, given explicitly,
any two of them at (Euclidean) distance at least `1`, and a positive integer `K ≤ |P|`. The
penny graph of `P` is the contact graph of the closed disks of diameter `1` centered at the
points of `P`: the disks have pairwise disjoint interiors, and two points are adjacent when
their disks touch, that is, when their distance is exactly `1`.
QUESTION: is there a dominating set of at most `K` points in the penny graph?

This is the restriction of DOMINATING SET IN UNIT DISK GRAPHS
(`WantedExt.Complexity.NPComplete.UnitDiskDominatingSetWanted`) to point sets with pairwise
distances at least `1`. The instance type, `UnitDiskDominatingSet.WellFormed` (positive
denominators, distinct points, `1 ≤ K ≤ |P|`) and `UnitDiskDominatingSetFeasible` are reused
unchanged; the separation condition is added to well-formedness. On such a point set the unit
disk graph (adjacency at distance at most `1`) is the penny graph (adjacency at distance exactly
`1`).

The points are given with rational coordinates, as in the unit disk statement. Three pairwise
touching pennies would need an equilateral triangle, which has no rational realization, so the
graphs represented here are triangle-free; they include all grid graphs (points of `ℤ²`, where
two points are adjacent exactly when they differ by `1` in one coordinate), on which Clark,
Colbourn and Johnson prove DOMINATING SET NP-complete and de Berg et al. give a polynomial
reduction from 3-SAT.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DOMINATING SET IN UNIT DISK GRAPHS instance
whose points are pairwise at distance at least `1`. -/
def WellFormed (i : UnitDiskDominatingSetInstance) : Prop :=
  UnitDiskDominatingSet.WellFormed i ∧
    ∀ a b : Fin i.1.length, a ≠ b → 1 ≤ dist (point i.1[a]) (point i.1[b])

open Classical in
/-- DOMINATING SET IN PENNY GRAPHS as a decision problem over bitstrings. -/
noncomputable def pennyGraphDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitDiskDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ UnitDiskDominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET IN PENNY GRAPHS is NP-complete.** Source: Clark, Colbourn and Johnson
(1990); de Berg et al. (2020); ISGCI (`gc_1381`); Garey and Johnson (1979), [GT2]. -/
public theorem_wanted pennyGraphDominatingSet_npComplete :
    pennyGraphDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pennyGraphDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.PennyGraphDominatingSet
