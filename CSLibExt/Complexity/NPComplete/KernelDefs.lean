/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KERNEL: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT57] KERNEL;
V. Chvátal, "On the computational complexity of finding a kernel", Report CRM-300, Centre de
recherches mathématiques, Université de Montréal (1973) (the author's reconstruction of the
proof: https://users.encs.concordia.ca/~chvatal/kernel.html);
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, d_out ≤ 2, d_in ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kernel

/-- An instance: the vertex count `n` and the arc list `A` (pairs `(u, v)` for arcs `u → v`). -/
abbrev KernelInstance := ℕ × List (ℕ × ℕ)

/-- The digraph of the instance on `Fin n`: `u → v` is an arc iff `(u, v)` is in the arc
list. -/
def Graph (i : KernelInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the arc list has no repeated arcs, its endpoints are
vertices, and it has no loops. -/
def WellFormed (i : KernelInstance) : Prop :=
  i.2.Nodup ∧ ∀ a ∈ i.2, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2

/-- A kernel: a vertex set with no arc between any two of its vertices, such that every vertex
outside it has an arc into it. -/
def KernelFeasible (i : KernelInstance) : Prop :=
  ∃ S : Finset (Fin i.1), (∀ u ∈ S, ∀ v ∈ S, ¬ (Graph i).Adj u v) ∧
    ∀ u ∉ S, ∃ v ∈ S, (Graph i).Adj u v

open Classical in
/-- KERNEL as a decision problem over bitstrings. -/
noncomputable def kernelDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KernelInstance) x with
  | some i => decide (WellFormed i ∧ KernelFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Kernel
