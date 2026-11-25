/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# d-COLLAPSIBILITY is NP-complete for every fixed d ≥ 4

Source:
M. Tancer, "d-collapsibility is NP-complete for d ≥ 4", Chicago Journal of Theoretical
Computer Science 2010, Article 3, doi:10.4086/cjtcs.2010.003 (Theorem 1.1(ii)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Combinatorics.RationalSimplicialHomologyShared

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DCollapsibility

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared (IsSimplicialComplex IsFacet)

/-!
# d-COLLAPSIBILITY is NP-complete for every fixed d ≥ 4

Fix an integer `d ≥ 4`. INSTANCE: a finite (abstract) simplicial complex `K`, that is, a finite
set system closed under taking subsets. QUESTION: is `K` `d`-collapsible?

Tancer's definitions: a face `σ` of `K` is collapsible if there is a unique inclusionwise
maximal face `τ(σ)` of `K` containing `σ` (`τ(σ) = σ` is allowed), and `d`-collapsible if moreover
`dim σ ≤ d - 1`, that is, `|σ| ≤ d`. For such `σ`, the complex `K \ [σ, τ(σ)]`, where
`[σ, τ(σ)] = {η ∈ K | σ ⊆ η ⊆ τ(σ)}`, arises from `K` by an elementary `d`-collapse. `K` is
`d`-collapsible if a sequence of elementary `d`-collapses reduces it to the empty complex `∅`
(the set system with no faces, not even the empty face). The size of an instance is the number
of faces of `K`.

Complexes are the repository's finite abstract simplicial complexes on the vertex set `ℕ`
(`WantedExt.Combinatorics.RationalSimplicialHomologyShared`): finite families of finite sets
closed under taking subsets (`IsSimplicialComplex`), so a nonempty complex contains the empty
face; maximal faces are `IsFacet`. The instance is the list of all faces of `K`, each a list of
distinct vertices, every face listed once, as in Tancer's input; `complex` reads it as a
`Finset (Finset ℕ)`. Unlike the ordinary collapses of `CollapseToOneComplexWanted`, the face
`σ` of an elementary `d`-collapse may be empty or maximal, and has at most `d` vertices.

Tancer proves `d`-COLLAPSIBILITY NP-complete for every fixed `d ≥ 4` (Theorem 1.1(ii)) and
polynomial for `d ≤ 2`; the case `d = 3` is left open there.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **d-COLLAPSIBILITY is NP-complete for every fixed `d ≥ 4`.** Source: Tancer (2010),
Theorem 1.1(ii). -/
public theorem_wanted dCollapsibility_npComplete (d : ℕ) (hd : 4 ≤ d) :
    dCollapsibilityDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (dCollapsibilityDec d)

end MetaMathlibExt.Complexity.NPComplete.DCollapsibility
