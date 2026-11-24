/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOMOLOGY LOCALIZATION (one-dimensional, over Z₂) is NP-complete

Source:
C. Chen and D. Freedman, "Hardness results for homology localization", Discrete and
Computational Geometry 45 (2011), 425-448, doi:10.1007/s00454-010-9322-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.SymmDiff
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Combinatorics.RationalSimplicialHomologyShared

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HomologyLocalization

open scoped symmDiff
open MathlibExt.Combinatorics.RationalSimplicialHomologyShared (IsSimplicialComplex)

/-!
# HOMOLOGY LOCALIZATION (one-dimensional, over Z₂) is NP-complete

INSTANCE: a finite simplicial complex `K`, a one-dimensional cycle `z` of `K` over `Z₂`, and a
natural number `k`. QUESTION: is there a one-dimensional cycle `z'` of `K` over `Z₂` that is
homologous to `z` and has at most `k` edges?

Over `Z₂` a one-dimensional chain is a set of edges (one-dimensional faces) of `K`, and the sum
of two chains is their symmetric difference. The boundary of an edge `{a, b}` is `{a} + {b}`,
so a chain `c` is a cycle exactly when every vertex lies in an even number of edges of `c`. The
boundary of a set `T` of triangles (two-dimensional faces) is the set of edges that lie in an
odd number of triangles of `T`. Two cycles `z, z'` are homologous when `z + z' = ∂T` for some
set `T` of triangles. The number of edges of `z'` is its volume (1-norm), the measure of
Chen and Freedman's volume localization.

Complexes are the repository's finite abstract simplicial complexes on the vertex set `ℕ`
(`WantedExt.Combinatorics.RationalSimplicialHomologyShared`): finite families of finite sets
closed under taking subsets (`IsSimplicialComplex`). The instance lists all faces of `K`, each
a list of distinct vertices, every face listed once. The cycle `z` is a list of distinct edges
of `K`.

Chen and Freedman prove that localizing a given homology class over `Z₂` with a cycle of
minimal volume is NP-hard, indeed NP-hard to approximate within any constant factor, already
for one-dimensional classes. Membership in NP: `z'` and the set `T` of triangles are a
certificate of size at most the number of faces of `K`, checked by parity counts. The bound
`k` may be `0`, when the question asks whether `z` is a boundary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the faces of the complex, the edges of the cycle `z`, and the bound `k`. -/
abbrev HomologyLocalizationInstance := List (List ℕ) × List (List ℕ) × ℕ

/-- The complex of the instance as a set system: the set of its faces. -/
def complex (i : HomologyLocalizationInstance) : Finset (Finset ℕ) :=
  (i.1.map List.toFinset).toFinset

/-- The cycle `z` of the instance as a set of edges. -/
def cycle (i : HomologyLocalizationInstance) : Finset (Finset ℕ) :=
  (i.2.1.map List.toFinset).toFinset

/-- Well-formedness of an instance: the faces list distinct vertices, no face is listed twice,
and the faces are closed under taking subsets; the edges of `z` are distinct two-vertex faces of
the complex, and every vertex lies in an even number of them, so `z` is a cycle. -/
def WellFormed (i : HomologyLocalizationInstance) : Prop :=
  (∀ f ∈ i.1, f.Nodup) ∧ (i.1.map List.toFinset).Nodup ∧
    IsSimplicialComplex (complex i) ∧
    (i.2.1.map List.toFinset).Nodup ∧
    (∀ e ∈ cycle i, e ∈ complex i ∧ e.card = 2) ∧
    ∀ v : ℕ, Even ((cycle i).filter (v ∈ ·)).card

/-- Some cycle `z'` with at most `k` edges is homologous to `z`: `z'` is a set of edges of the
complex in which every vertex lies in an even number of edges, and for some set `T` of
triangles of the complex, an edge lies in exactly one of `z` and `z'` exactly when it lies in an
odd number of triangles of `T` (that is, `z + z' = ∂T` over `Z₂`). -/
def HomologyLocalizationFeasible (i : HomologyLocalizationInstance) : Prop :=
  ∃ z' T : Finset (Finset ℕ),
    (∀ e ∈ z', e ∈ complex i ∧ e.card = 2) ∧ (∀ v : ℕ, Even (z'.filter (v ∈ ·)).card) ∧
    (∀ t ∈ T, t ∈ complex i ∧ t.card = 3) ∧
    (∀ e ∈ complex i, e.card = 2 → (e ∈ cycle i ∆ z' ↔ Odd (T.filter (e ⊆ ·)).card)) ∧
    z'.card ≤ i.2.2

open Classical in
/-- HOMOLOGY LOCALIZATION as a decision problem over bitstrings. -/
noncomputable def homologyLocalizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HomologyLocalizationInstance) x with
  | some i => decide (WellFormed i ∧ HomologyLocalizationFeasible i)
  | none => false

/-- **HOMOLOGY LOCALIZATION (one-dimensional, over `Z₂`) is NP-complete.** Source: Chen and
Freedman (2011). -/
public theorem_wanted homologyLocalization_npComplete :
    homologyLocalizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L homologyLocalizationDec

end MetaMathlibExt.Complexity.NPComplete.HomologyLocalization
