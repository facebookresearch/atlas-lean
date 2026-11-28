/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CORRELATION CLUSTERING: definitions

Source:
N. Bansal, A. Blum and S. Chawla, "Correlation clustering", Machine Learning 56 (2004),
89-113, doi:10.1023/B:MACH.0000033116.57574.95, Section 3 (decision version of minimizing
disagreements; reduction from PARTITION INTO TRIANGLES).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CorrelationClustering

/-- An instance: the rows of the `n × n` label matrix (`true` is `+`, `false` is `-`) and the
bound `K`. -/
abbrev CorrelationClusteringInstance := List (List Bool) × ℕ

/-- The label of the edge `{u, v}`: entry `(u, v)` of the matrix (`false` outside it). -/
def label (i : CorrelationClusteringInstance) (u v : ℕ) : Bool :=
  (i.1.getD u []).getD v false

/-- Well-formedness of an instance: the label matrix is square and symmetric. -/
def WellFormed (i : CorrelationClusteringInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧
    ∀ u < i.1.length, ∀ v < i.1.length, label i u v = label i v u

/-- The number of disagreements of the clustering `c`: the edges `{u, v}` (`u < v`) labeled `+`
whose endpoints lie in different clusters, plus those labeled `-` whose endpoints lie in the
same cluster. -/
def disagreements (i : CorrelationClusteringInstance) (c : Fin i.1.length → Fin i.1.length) :
    ℕ :=
  ((Finset.univ : Finset (Fin i.1.length × Fin i.1.length)).filter fun e =>
    e.1 < e.2 ∧
      ((label i e.1 e.2 = true ∧ c e.1 ≠ c e.2) ∨
        (label i e.1 e.2 = false ∧ c e.1 = c e.2))).card

/-- Some clustering has at most `K` disagreements. -/
def CorrelationClusteringFeasible (i : CorrelationClusteringInstance) : Prop :=
  ∃ c : Fin i.1.length → Fin i.1.length, disagreements i c ≤ i.2

open Classical in
/-- CORRELATION CLUSTERING as a decision problem over bitstrings. -/
noncomputable def correlationClusteringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CorrelationClusteringInstance) x with
  | some i => decide (WellFormed i ∧ CorrelationClusteringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CorrelationClustering
