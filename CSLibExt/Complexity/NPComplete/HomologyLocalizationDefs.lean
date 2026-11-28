/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOMOLOGY LOCALIZATION (one-dimensional, over Z₂): definitions

Source:
C. Chen and D. Freedman, "Hardness results for homology localization", Discrete and
Computational Geometry 45 (2011), 425-448, doi:10.1007/s00454-010-9322-8.
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.SymmDiff
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.RationalSimplicialHomologyShared

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HomologyLocalization

open scoped symmDiff
open MathlibExt.Combinatorics.RationalSimplicialHomologyShared (IsSimplicialComplex)

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

end MetaMathlibExt.Complexity.NPComplete.HomologyLocalization
