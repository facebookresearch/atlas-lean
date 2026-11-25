/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view) is NP-complete

Source:
P. Buneman, S. Khanna and W.-C. Tan, "On propagation of deletions and annotations through
views", Proceedings of the 21st ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database
Systems (PODS 2002), 150-158, doi:10.1145/543613.543633 (Section 2.1.1, Theorem 2.1: deciding
whether there is a side-effect-free deletion is NP-hard for the project-join query
`Π_{A,C}(R₁(A, B) ⋈ R₂(B, C))`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Databases.RelationalAlgebra
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SideEffectFreeDeletionPropagation

open Cslib.Databases

/-!
# SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view) is NP-complete

The view is the fixed project-join query `V = Π_{A,C}(R₁ ⋈ R₂)` over two binary relations
`R₁(A, B)` and `R₂(B, C)`.
INSTANCE: a source database, that is, relations `R₁` over `(A, B)` and `R₂` over `(B, C)`, and a
tuple `t` of the view `V(R₁, R₂)`.
QUESTION: is there a set of source tuples `T₁ ⊆ R₁`, `T₂ ⊆ R₂` whose deletion is
side-effect-free: it removes `t` from the view and no other view tuple, i.e.
`V(R₁ \ T₁, R₂ \ T₂) = V(R₁, R₂) \ {t}`?

Buneman, Khanna and Tan prove this NP-hard by a reduction from monotone 3SAT that uses exactly
this query ("The result is true even when the query is of constant size and only involves two
relations"); for a fixed query the problem is in NP, since the view is computed in polynomial
time.

Representation: the relational algebra of `CSLibExt.Databases.RelationalAlgebra` (named model,
tuples `Fin 3 → Option ℕ`, `join` the natural join, `project` the projection), with attributes
`A = 0`, `B = 1`, `C = 2` and values in `ℕ`. A relation is given as a list of pairs without
repetitions: `(a, b)` in `R₁` is the tuple with `A = a`, `B = b`, and `(b, c)` in `R₂` the tuple
with `B = b`, `C = c`; the view tuple `t = (a, c)` is the tuple with `A = a`, `C = c`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SIDE-EFFECT-FREE DELETION PROPAGATION for the project-join view `Π_{A,C}(R₁ ⋈ R₂)` is
NP-complete.** Source: Buneman, Khanna and Tan (2002), Theorem 2.1. -/
public theorem_wanted sideEffectFreeDeletionPropagation_npComplete :
    sideEffectFreeDeletionPropagationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sideEffectFreeDeletionPropagationDec

end MetaMathlibExt.Complexity.NPComplete.SideEffectFreeDeletionPropagation
