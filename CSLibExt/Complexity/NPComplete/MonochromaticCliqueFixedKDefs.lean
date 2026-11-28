/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOCHROMATIC K_k is NP-complete for every fixed k ≥ 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT6] MONOCHROMATIC
TRIANGLE (p. 191), comment "Variants in which 'triangle' is replaced by any larger fixed complete
graph are also NP-complete [Burr, 1976]";
S. A. Burr, "On the computational complexity of Ramsey-type problems", in *Mathematics of Ramsey
Theory* (J. Nešetřil and V. Rödl, eds.), Algorithms and Combinatorics 5, Springer (1990), 46-52,
doi:10.1007/978-3-642-72905-8_5 (as recorded by M. Schaefer, "Graph Ramsey theory and the
polynomial hierarchy", Journal of Computer and System Sciences 62 (2001), 290-322,
doi:10.1006/jcss.2000.1729, p. 292: deciding `F → (G, H)` is coNP-complete for any fixed
3-connected graphs `G` and `H`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MonochromaticTriangleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonochromaticCliqueFixedK

open MetaMathlibExt.Complexity.NPComplete.MonochromaticTriangle
  (MonochromaticTriangleInstance Graph)

/-- The edges split into two parts neither of which contains `K_k`: a subgraph `G₁ ≤ G` such that
neither `G₁` nor its complement `G \ G₁` in `G` contains a `k`-clique. -/
def MonochromaticCliqueFeasible (k : ℕ) (i : MonochromaticTriangleInstance) : Prop :=
  ∃ G₁ : SimpleGraph (Fin i.1), G₁ ≤ Graph i ∧ G₁.CliqueFree k ∧ (Graph i \ G₁).CliqueFree k

open Classical in
/-- MONOCHROMATIC K_k, for the fixed `k`, as a decision problem over bitstrings. -/
noncomputable def monochromaticCliqueFixedKDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonochromaticTriangleInstance) x with
  | some i => decide (MonochromaticTriangle.WellFormed i ∧ MonochromaticCliqueFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MonochromaticCliqueFixedK
