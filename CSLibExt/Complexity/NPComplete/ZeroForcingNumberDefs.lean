/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZERO FORCING NUMBER: definitions

Source:
S. Fallat, K. Meagher and B. Yang, "On the complexity of the positive semidefinite zero forcing
number", Linear Algebra and its Applications 491 (2016), 101-122,
doi:10.1016/j.laa.2015.03.011, Corollary 3.4 (via B. Yang, "Fast-mixed searching and related
problems on graphs", Theoretical Computer Science 507 (2013), 100-113,
doi:10.1016/j.tcs.2013.04.015);
A. Aazami, *Hardness results and approximation algorithms for some problems on graphs*, PhD
thesis, University of Waterloo (2008), Theorem 2.3.1 (NP-hardness with node weights 0 and 1, on
planar graphs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ZeroForcingNumber

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- The vertices that end up black when the vertices of `S` start black and the zero forcing
color-change rule is applied: the least set of vertices containing `S` and closed under forcing.
-/
inductive Forced {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Fin n → Prop
  /-- The vertices of `S` are black. -/
  | init {v : Fin n} : v ∈ S → Forced G S v
  /-- A black vertex `u` whose neighbors other than `v` are all black forces its neighbor `v`.
  -/
  | force {u v : Fin n} : Forced G S u → G.Adj u v →
      (∀ w, G.Adj u w → w ≠ v → Forced G S w) → Forced G S v

/-- The graph has a zero forcing set of at most `K` vertices. -/
def ZeroForcingNumberFeasible (i : GraphColoringInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ ∀ v, Forced (Graph i) S v

open Classical in
/-- ZERO FORCING NUMBER as a decision problem over bitstrings. -/
noncomputable def zeroForcingNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (GraphColoring.WellFormed i ∧ ZeroForcingNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ZeroForcingNumber
