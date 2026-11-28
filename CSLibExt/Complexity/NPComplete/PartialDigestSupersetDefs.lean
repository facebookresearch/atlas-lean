/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL DIGEST SUPERSET: definitions

Source:
M. Cieliebak, S. Eidenbenz and P. Penna, "Noisy data make the partial digest problem NP-hard",
in *Algorithms in Bioinformatics (WABI 2003)*, Lecture Notes in Computer Science 2812 (2003),
111-123, doi:10.1007/978-3-540-39763-2_9; also Technical Report 381, Department of Computer
Science, ETH Zurich (2002), doi:10.3929/ethz-a-006665694, Section 2, Theorem 1 (MIN PARTIAL
DIGEST SUPERSET is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialDigestSuperset

/-- An instance: the distances `D` (a list read as a multiset) and the bound `t`. -/
abbrev PartialDigestSupersetInstance := List ℕ × ℕ

/-- Well-formedness of an instance: every distance is positive. -/
def WellFormed (i : PartialDigestSupersetInstance) : Prop :=
  ∀ d ∈ i.1, 0 < d

/-- The multiset `Δ(P)` of pairwise distances of a finite set of integers, one entry per pair of
points. -/
def distances (P : Finset ℤ) : Multiset ℕ :=
  (((P ×ˢ P).filter fun q => q.1 < q.2).val.map fun q => (q.2 - q.1).toNat)

/-- Some set `P` of at most `t` integers whose distance multiset contains `D`. -/
def PartialDigestSupersetFeasible (i : PartialDigestSupersetInstance) : Prop :=
  ∃ P : Finset ℤ, P.card ≤ i.2 ∧ (i.1 : Multiset ℕ) ≤ distances P

open Classical in
/-- PARTIAL DIGEST SUPERSET as a decision problem over bitstrings. -/
noncomputable def partialDigestSupersetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartialDigestSupersetInstance) x with
  | some i => decide (WellFormed i ∧ PartialDigestSupersetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialDigestSuperset
