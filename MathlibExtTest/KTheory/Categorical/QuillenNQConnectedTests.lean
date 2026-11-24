/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.ModuleCat.Biproducts
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.KTheory.Exact.Quillen.NQConnected

/-!
# Quillen nerve connectedness consumer tests

Consumer-style checks for the public zero-to-object layer over `ModuleCat ℚ`:
span type/orientation, morphism type/orientation, representative formula,
vertex-edge type, edge formula, edge source/target laws, and connectedness.
No implementation proofs are unfolded; no initial or zero object in `QuillenQ`,
contractibility, `π₀`-to-`K₀` identification, loops, higher K-groups,
weak equivalence, Q/S comparison, spectrum, or Milnor/Bloch-Kato claim is made.
-/

open CategoryTheory
open CategoryTheory.Limits
open Simplicial Opposite
open ZeroObject

/-- Zero-to-object span goes from `0` to `X` with apex `0`. -/
noncomputable example (X : ModuleCat ℚ) :
    AlgebraicKTheory.QuillenSpan (0 : ModuleCat ℚ) X :=
  AlgebraicKTheory.QuillenQ.zeroToObjectSpan X

/-- Zero-to-object morphism goes from `⟨0⟩` to `⟨X⟩`. -/
noncomputable example (X : ModuleCat ℚ) :
    (⟨0⟩ : AlgebraicKTheory.QuillenQ (ModuleCat ℚ)) ⟶ ⟨X⟩ :=
  AlgebraicKTheory.QuillenQ.zeroToObjectHom X

/-- Representative formula for the zero-to-object morphism. -/
example (X : ModuleCat ℚ) :
    AlgebraicKTheory.QuillenQ.zeroToObjectHom X =
      AlgebraicKTheory.QuillenQ.mkHom
        (AlgebraicKTheory.QuillenQ.zeroToObjectSpan X) :=
  AlgebraicKTheory.QuillenQ.zeroToObjectHom_mk X

/-- Zero-to-vertex edge goes from the zero vertex to `mk₀ ⟨X⟩`. -/
noncomputable example (X : ModuleCat ℚ) :
    (AlgebraicKTheory.NQ (ModuleCat ℚ)).Edge
      (AlgebraicKTheory.NQ.zeroVertex (ModuleCat ℚ))
      (ComposableArrows.mk₀ (⟨X⟩ : AlgebraicKTheory.QuillenQ (ModuleCat ℚ))) :=
  AlgebraicKTheory.NQ.zeroToVertexEdge X

/-- Zero-to-vertex edge unfolds to the zero-to-object morphism. -/
example (X : ModuleCat ℚ) :
    (AlgebraicKTheory.NQ.zeroToVertexEdge X).edge =
      ComposableArrows.mk₁ (AlgebraicKTheory.QuillenQ.zeroToObjectHom X) :=
  AlgebraicKTheory.NQ.zeroToVertexEdge_edge X

/-- Zero-to-vertex edge starts at the zero vertex (`δ 1` source). -/
example (X : ModuleCat ℚ) :
    (AlgebraicKTheory.NQ (ModuleCat ℚ)).δ 1
        (AlgebraicKTheory.NQ.zeroToVertexEdge X).edge =
      AlgebraicKTheory.NQ.zeroVertex (ModuleCat ℚ) :=
  AlgebraicKTheory.NQ.zeroToVertexEdge_src X

/-- Zero-to-vertex edge ends at `mk₀ ⟨X⟩` (`δ 0` target). -/
example (X : ModuleCat ℚ) :
    (AlgebraicKTheory.NQ (ModuleCat ℚ)).δ 0
        (AlgebraicKTheory.NQ.zeroToVertexEdge X).edge =
      ComposableArrows.mk₀ (⟨X⟩ : AlgebraicKTheory.QuillenQ (ModuleCat ℚ)) :=
  AlgebraicKTheory.NQ.zeroToVertexEdge_tgt X

/-- The Quillen nerve over `ModuleCat ℚ` is connected. -/
noncomputable example :
    (AlgebraicKTheory.NQ (ModuleCat ℚ)).IsConnected :=
  AlgebraicKTheory.NQ.isConnected (ModuleCat ℚ)
