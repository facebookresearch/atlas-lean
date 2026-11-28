/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view): definitions

Source:
P. Buneman, S. Khanna and W.-C. Tan, "On propagation of deletions and annotations through
views", Proceedings of the 21st ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database
Systems (PODS 2002), 150-158, doi:10.1145/543613.543633 (Section 2.1.1, Theorem 2.1: deciding
whether there is a side-effect-free deletion is NP-hard for the project-join query
`Π_{A,C}(R₁(A, B) ⋈ R₂(B, C))`).
-/
module

public import CSLibExt.Databases.RelationalAlgebra
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SideEffectFreeDeletionPropagation

open Cslib.Databases

/-- An instance: the pairs of `R₁(A, B)`, the pairs of `R₂(B, C)`, and the view tuple
`t = (a, c)`. -/
abbrev SideEffectFreeDeletionPropagationInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The tuple with value `u` at attribute `x`, value `v` at attribute `y`, and undefined
elsewhere (for `x ≠ y`). -/
def pairTuple (x y : Fin 3) (u v : ℕ) : Tuple (Fin 3) ℕ :=
  fun k => if k = x then some u else if k = y then some v else none

/-- The relation `R₁` over the attributes `A = 0`, `B = 1`. -/
def rel₁ (i : SideEffectFreeDeletionPropagationInstance) : Finset (Tuple (Fin 3) ℕ) :=
  (i.1.map fun p => pairTuple 0 1 p.1 p.2).toFinset

/-- The relation `R₂` over the attributes `B = 1`, `C = 2`. -/
def rel₂ (i : SideEffectFreeDeletionPropagationInstance) : Finset (Tuple (Fin 3) ℕ) :=
  (i.2.1.map fun p => pairTuple 1 2 p.1 p.2).toFinset

/-- The view `Π_{A,C}(r₁ ⋈ r₂)`. -/
def view (r₁ r₂ : Finset (Tuple (Fin 3) ℕ)) : Finset (Tuple (Fin 3) ℕ) :=
  project {0, 2} (join r₁ r₂)

/-- The view tuple `t = (a, c)` over the attributes `A = 0`, `C = 2`. -/
def target (i : SideEffectFreeDeletionPropagationInstance) : Tuple (Fin 3) ℕ :=
  pairTuple 0 2 i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: the relations are listed without repetitions, and `t` is
a tuple of the view. -/
def WellFormed (i : SideEffectFreeDeletionPropagationInstance) : Prop :=
  i.1.Nodup ∧ i.2.1.Nodup ∧ target i ∈ view (rel₁ i) (rel₂ i)

/-- Some deletion of source tuples `T₁ ⊆ R₁`, `T₂ ⊆ R₂` removes exactly `t` from the view. -/
def SideEffectFreeDeletionPropagationFeasible
    (i : SideEffectFreeDeletionPropagationInstance) : Prop :=
  ∃ T₁ ⊆ rel₁ i, ∃ T₂ ⊆ rel₂ i,
    view (rel₁ i \ T₁) (rel₂ i \ T₂) = (view (rel₁ i) (rel₂ i)).erase (target i)

open Classical in
/-- SIDE-EFFECT-FREE DELETION PROPAGATION for `Π_{A,C}(R₁ ⋈ R₂)` as a decision problem over
bitstrings. -/
noncomputable def sideEffectFreeDeletionPropagationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SideEffectFreeDeletionPropagationInstance) x with
  | some i => decide (WellFormed i ∧ SideEffectFreeDeletionPropagationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SideEffectFreeDeletionPropagation
