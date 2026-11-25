/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Finite ambient cells contained in a finite subcomplex

For `A : X.Subcomplex` with `[SSet.Finite (A : SSet)]`, the ambient
nondegenerate cells `s : X.N` satisfying `s.subcomplex ≤ A` (equivalently
`s.simplex ∈ A.obj _`) form a finite type. This is the smallest public fact
the closed-discrete selector caller needs.

API-reuse map (all `reuse`; no `local` invention): already-finite
`(A : SSet).N` from `SSet.Finite`, mono injectivity of `A.ι.app`
(`injective_of_mono`), nondegeneracy reflection
`SSet.Subcomplex.mem_nonDegenerate_iff`, membership coherence
`SSet.Subcomplex.ofSimplex_le_iff`, equality characterization
`SSet.N.ext_iff`, and finiteness transport `Finite.of_injective`.

Nonclaims: no colimit, topology, product comparison, weak-equivalence,
model-category, or general subcomplex lattice content appears here.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SSet
namespace Subcomplex

universe u

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- Ambient nondegenerate cells whose generated subcomplex lies in `A`. -/
abbrev AmbientCells := { s : X.N // s.subcomplex ≤ A }

/-- Membership coherence: the subcomplex condition is membership of the
representative simplex. -/
lemma mem_ambientCells_iff (s : X.N) :
    s.subcomplex ≤ A ↔ s.simplex ∈ A.obj _ :=
  Subcomplex.ofSimplex_le_iff _ _

variable [SSet.Finite (A : SSet.{u})]

/-- Forward map of ambient cells into the already-finite `(A : SSet).N`. -/
def ambientCellsFun (a : AmbientCells A) : (A : SSet.{u}).N :=
  SSet.N.mk (X := (A : SSet.{u}))
    ⟨a.val.simplex, (Subcomplex.ofSimplex_le_iff _ _).mp a.property⟩
    ((Subcomplex.mem_nonDegenerate_iff A _).mpr a.val.nonDegenerate)

/-- Embedding of ambient cells into the already-finite `(A : SSet).N`. -/
def ambientCellsEmbedding : AmbientCells A ↪ (A : SSet.{u}).N where
  toFun := ambientCellsFun A
  inj' a b h := by
    have hS : (ambientCellsFun A a).toS = (ambientCellsFun A b).toS := by
      exact (SSet.N.ext_iff _ _).mp h
    have hmap : S.map A.ι (ambientCellsFun A a).toS =
        S.map A.ι (ambientCellsFun A b).toS := by
      rw [hS]
    have hab : a.val.toS = b.val.toS := by
      have e1 : S.map A.ι (ambientCellsFun A a).toS = a.val.toS := rfl
      have e2 : S.map A.ι (ambientCellsFun A b).toS = b.val.toS := rfl
      rw [e1] at hmap
      rw [e2] at hmap
      exact hmap
    have hN : a.val = b.val := (SSet.N.ext_iff _ _).mpr hab
    exact Subtype.ext hN

instance : Finite (AmbientCells A) :=
  Finite.of_injective (ambientCellsEmbedding A) (ambientCellsEmbedding A).injective

end Subcomplex
end SSet
