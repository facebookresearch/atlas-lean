/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# d-COLLAPSIBILITY is NP-complete for every fixed d ≥ 4: definitions

Source:
M. Tancer, "d-collapsibility is NP-complete for d ≥ 4", Chicago Journal of Theoretical
Computer Science 2010, Article 3, doi:10.4086/cjtcs.2010.003 (Theorem 1.1(ii)).
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.RationalSimplicialHomologyShared

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DCollapsibility

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared (IsSimplicialComplex IsFacet)

/-- An instance: the faces of the complex, each a list of vertex labels. -/
abbrev DCollapsibilityInstance := List (List ℕ)

/-- The complex of the instance as a set system: the set of its faces. -/
def complex (i : DCollapsibilityInstance) : Finset (Finset ℕ) :=
  (i.map List.toFinset).toFinset

/-- Well-formedness of an instance: every face lists distinct vertices, no face is listed
twice, and the faces are closed under taking subsets, so they form a simplicial complex. -/
def WellFormed (i : DCollapsibilityInstance) : Prop :=
  (∀ f ∈ i, f.Nodup) ∧ (i.map List.toFinset).Nodup ∧ IsSimplicialComplex (complex i)

/-- `K'` arises from `K` by an elementary `d`-collapse: some face `σ` of `K` with `|σ| ≤ d`
(dimension at most `d - 1`) lies in a unique maximal face `τ` of `K` (`τ = σ` allowed), and `K'`
is `K` with the faces `η`, `σ ⊆ η ⊆ τ`, removed. -/
def ElementaryCollapse (d : ℕ) (K K' : Finset (Finset ℕ)) : Prop :=
  ∃ σ ∈ K, σ.card ≤ d ∧ ∃ τ ∈ K, IsFacet K τ ∧ σ ⊆ τ ∧
    (∀ τ' ∈ K, IsFacet K τ' → σ ⊆ τ' → τ' = τ) ∧
    K' = K.filter fun η => ¬ (σ ⊆ η ∧ η ⊆ τ)

/-- The complex is `d`-collapsible: a finite sequence of elementary `d`-collapses reduces it to
the empty complex. -/
def DCollapsibilityFeasible (d : ℕ) (i : DCollapsibilityInstance) : Prop :=
  Relation.ReflTransGen (ElementaryCollapse d) (complex i) ∅

open Classical in
/-- d-COLLAPSIBILITY, for the fixed `d`, as a decision problem over bitstrings. -/
noncomputable def dCollapsibilityDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DCollapsibilityInstance) x with
  | some i => decide (WellFormed i ∧ DCollapsibilityFeasible d i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DCollapsibility
