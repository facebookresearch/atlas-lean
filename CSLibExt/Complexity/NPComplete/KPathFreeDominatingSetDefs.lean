/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-PATH-FREE DOMINATING SET (directed): definitions

Source:
R. Bar-Yehuda and U. Vishkin, "Complexity of finding k-path-free dominating sets in graphs",
Information Processing Letters 14 (1982), 228-232, doi:10.1016/0020-0190(82)90021-7.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.KernelDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KPathFreeDominatingSet

open Kernel (KernelInstance Graph WellFormed)

/-- `S` contains a (simple, directed) path with `k` vertices: distinct vertices
`p 0, …, p (k - 1)` of `S` with an arc `p j → p (j + 1)` for every `j + 1 < k`. -/
def HasPathIn {V : Type*} (G : Digraph V) (S : Finset V) (k : ℕ) : Prop :=
  ∃ p : Fin k → V, Function.Injective p ∧ (∀ j, p j ∈ S) ∧
    ∀ (j : Fin k) (h : j.val + 1 < k), G.Adj (p j) (p ⟨j.val + 1, h⟩)

/-- A `k`-path-free dominating set: a vertex set `S` such that every vertex `y ∉ S` has an arc
`x → y` from some `x ∈ S`, and `S` contains no path with `k` vertices. -/
def KPathFreeDominatingSetFeasible (k : ℕ) (i : KernelInstance) : Prop :=
  ∃ S : Finset (Fin i.1), (∀ y ∉ S, ∃ x ∈ S, (Graph i).Adj x y) ∧ ¬ HasPathIn (Graph i) S k

open Classical in
/-- k-PATH-FREE DOMINATING SET, for the fixed `k`, as a decision problem over bitstrings. -/
noncomputable def kPathFreeDominatingSetDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := KernelInstance) x with
  | some i => decide (WellFormed i ∧ KPathFreeDominatingSetFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KPathFreeDominatingSet
