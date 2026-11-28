/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIXED-POINT-FREE AUTOMORPHISM OF ORDER 2: definitions

Source:
A. Lubiw, "Some NP-complete problems similar to graph isomorphism", SIAM Journal on Computing
10 (1981), 11-21, doi:10.1137/0210002 (original not available here; the abstract: "the problem of
determining whether a given graph has a fixed-point-free automorphism" is NP-complete);
A. Abiad, G. Coutinho, E. Juliano, V. F. dos Santos and S. Zeijlemaker, "Computing fixed point
free automorphisms of graphs", arXiv:2603.26006 (2026), Section 1 ("FPF involutions, that is,
FPF automorphisms of order two. The problem of finding involutions without fixed points
(FPFInv) is also NP-hard [Lubiw]").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.OrderOfElement
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedPointFreeInvolution

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev FixedPointFreeInvolutionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : FixedPointFreeInvolutionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : FixedPointFreeInvolutionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph has an automorphism of order `2` that fixes no vertex. -/
def FixedPointFreeInvolutionFeasible (i : FixedPointFreeInvolutionInstance) : Prop :=
  ∃ f : Graph i ≃g Graph i, orderOf f = 2 ∧ ∀ v, f v ≠ v

open Classical in
/-- FIXED-POINT-FREE AUTOMORPHISM OF ORDER 2 as a decision problem over bitstrings. -/
noncomputable def fixedPointFreeInvolutionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedPointFreeInvolutionInstance) x with
  | some i => decide (WellFormed i ∧ FixedPointFreeInvolutionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FixedPointFreeInvolution
