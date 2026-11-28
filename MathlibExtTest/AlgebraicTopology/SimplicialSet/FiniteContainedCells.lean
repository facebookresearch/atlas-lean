/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/
module

import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteGeneratedSubcomplex
import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteSubcomplexCells
import MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateEmbedding
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex

/-!
# Contained cells of a finite simplicial subcomplex

For the full subcomplex of Δ[0], the contained-cell type contains its vertex and embeds
into the nondegenerate simplices of the carrier. The type of ambient simplices missing
from this full subcomplex is empty. The coordinate comparisons therefore distinguish the
carrier from its complement. Finite families of dimension-varying generators are also used.
-/

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

namespace MathlibExtTest.FiniteContainedCells

universe u

example {X : SSet.{u}} (A : X.Subcomplex) :
    SSet.Subcomplex.AmbientCells A ↪ (A : SSet.{u}).N :=
  SSet.Subcomplex.ambientCellsEmbedding A

example {X : SSet.{u}} (A : X.Subcomplex) [SSet.Finite (A : SSet.{u})] :
    Finite (SSet.Subcomplex.AmbientCells A) := inferInstance

example {X : SSet.{u}} (A : X.Subcomplex) (a : SSet.Subcomplex.AmbientCells A) :
    (SSet.Subcomplex.ambientCellsEmbedding A a).dim = a.val.dim := rfl

example {X : SSet.{u}} (A : X.Subcomplex) (a : SSet.Subcomplex.AmbientCells A) :
    (SSet.Subcomplex.ambientCellsEmbedding A a).simplex.val = a.val.simplex := rfl

example (X : SSet.{u}) (s : Fin 2 → Σ n, X _⦋n⦌) :
    SSet.Finite ((⨆ i, SSet.Subcomplex.ofSimplex (s i).2 : X.Subcomplex) : SSet.{u}) :=
  SSet.Subcomplex.finite_iSup_ofSimplex X s

private abbrev point : SSet.{0} := Δ[0]
private abbrev full : point.Subcomplex := ⊤

private instance fullFinite : SSet.Finite (full : SSet.{0}) :=
  SSet.finite_of_mono full.ι

private def vertex : point _⦋0⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)

private theorem vertex_nonDegenerate : vertex ∈ point.nonDegenerate 0 :=
  (SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono (𝟙 ⦋0⦌)).mpr inferInstance

private def ambientVertex : SSet.Subcomplex.AmbientCells full :=
  ⟨SSet.N.mk vertex vertex_nonDegenerate, le_top⟩

example : Nonempty (SSet.Subcomplex.AmbientCells full) := ⟨ambientVertex⟩

example : IsEmpty full.N :=
  ⟨fun s => s.notMem (by trivial)⟩

example : (SSet.Subcomplex.ambientCellsEmbedding full ambientVertex).dim = 0 := rfl

example : (SSet.Subcomplex.ambientCellsEmbedding full ambientVertex).simplex.val = vertex := rfl

example :
    (SSet.nonDegenerateEmbeddingOfMono full.ι 0
      ⟨⟨vertex, by trivial⟩,
        (SSet.Subcomplex.mem_nonDegenerate_iff full _).mpr vertex_nonDegenerate⟩).val = vertex :=
  rfl

end MathlibExtTest.FiniteContainedCells
