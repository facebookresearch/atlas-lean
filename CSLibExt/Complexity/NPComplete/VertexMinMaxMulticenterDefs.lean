/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX MIN-MAX MULTICENTER (centers at vertices): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER, comment
(p. 220): "Variant in which we must choose a subset `P ⊆ V` is also NP-complete but solvable for
fixed `K` and for trees [Slater, 1976]";
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinMaxMulticenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexMinMaxMulticenter

open MinMaxMulticenter (MinMaxMulticenterInstance Graph walkLength weight)

/-- Some set `P` of at most `K` vertices has, for every vertex `v`, a center `p ∈ P` and a walk
from `v` to `p` of total length `len` with `w(v) · len ≤ B`. -/
def VertexMinMaxMulticenterFeasible (i : MinMaxMulticenterInstance) : Prop :=
  ∃ P : Finset (Fin i.1), P.card ≤ i.2.2.2.1 ∧
    ∀ v : Fin i.1, ∃ p ∈ P, ∃ W : (Graph i).Walk v p,
      (weight i v : ℝ) * walkLength i W ≤ (i.2.2.2.2.1 : ℝ) / i.2.2.2.2.2

open Classical in
/-- VERTEX MIN-MAX MULTICENTER as a decision problem over bitstrings. -/
noncomputable def vertexMinMaxMulticenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinMaxMulticenterInstance) x with
  | some i => decide (MinMaxMulticenter.WellFormed i ∧ VertexMinMaxMulticenterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.VertexMinMaxMulticenter
