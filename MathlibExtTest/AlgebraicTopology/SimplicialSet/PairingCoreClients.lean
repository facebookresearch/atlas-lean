/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.PairingCellReader
import MathlibExt.AlgebraicTopology.SimplicialSet.PairingCoreTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexVertexCoverage
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-!
# Focused clients of pairing-core transport and the rank-cell readers

* Vertex coverage: every nondegenerate simplex outside a subcomplex that contains all vertices has
  dimension at least one. The horn `Λ[2, 1]` contains every vertex of `Δ[2]`, and the top simplex
  lies outside it. The vertex hypothesis is needed: the vertex of `Δ[0]` lies outside the empty
  subcomplex.
* Mathlib's regular pairing core for `Λ[m + 1, k.castSucc] ⊗ Δ[n] ∪ Δ[m + 1] ⊗ ∂Δ[n]`: its
  opposite core is again regular, so its pairing has a rank function with values in `ℕ`. Each rank
  cell of the opposite core has the dimension of the original type (II) simplex and misses the
  reversed face, and the opposite keeps the ancestral relation.
-/

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.PairingCoreClients

open SSet

/-! ### Vertex coverage -/

/-- The horn `Λ[2, 1]` contains every vertex of `Δ[2]`. -/
theorem horn_vertices (x : (Δ[2] : SSet.{u}) _⦋0⦌) :
    x ∈ (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).obj (op ⦋0⦌) := by
  simp

/-- So every nondegenerate simplex of `Δ[2]` outside the horn has dimension at least one. -/
theorem one_le_dim (s : (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).N) : 1 ≤ s.dim :=
  Subcomplex.N.one_le_dim_of_vertices horn_vertices s

/-- The top simplex of `Δ[2]` lies outside the horn. -/
noncomputable def top : (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).N :=
  Subcomplex.N.mk (stdSimplex.objEquiv.symm (𝟙 ⦋2⦌))
    ((stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono _).mpr inferInstance)
    (objEquiv_symm_notMem_horn_of_isIso 1 (𝟙 ⦋2⦌))

example : top.{u}.dim = 2 :=
  rfl

/-- Without the vertex hypothesis the bound fails: the vertex of `Δ[0]` lies outside the empty
subcomplex and has dimension zero. -/
noncomputable def vertex : (⊥ : (Δ[0] : SSet.{u}).Subcomplex).N :=
  Subcomplex.N.mk (n := 0) (stdSimplex.obj₀Equiv.symm 0) (by simp [nonDegenerate_zero]) (by simp)

theorem vertex_dim : vertex.{u}.dim = 0 :=
  rfl

example : ¬ ∀ s : (⊥ : (Δ[0] : SSet.{u}).Subcomplex).N, 1 ≤ s.dim :=
  fun h => absurd (h vertex) (by rw [vertex_dim]; decide)

/-! ### Transport of Mathlib's regular pairing core -/

variable {m : ℕ} (k : Fin (m + 1)) (n : ℕ)

/-- Mathlib's pairing core for `Λ[m + 1, k.castSucc] ⊗ Δ[n] ∪ Δ[m + 1] ⊗ ∂Δ[n]`. -/
noncomputable abbrev core :=
  prodStdSimplex.pairingCore.{u} k n

/-- Its opposite core is again regular. -/
example : (core.{u} k n).op.IsRegular :=
  inferInstance

/-- So the opposite pairing has a rank function with values in `ℕ`. -/
noncomputable abbrev opRank : (core.{u} k n).op.pairing.RankFunction ℕ :=
  (core.{u} k n).op.pairing.rankFunction

/-- The opposite core has the original indices and dimensions, and reverses each face index. -/
example (s : (core.{u} k n).ι) :
    (core.{u} k n).op.dim s = s.d ∧ (core.{u} k n).op.index s = s.index.castSucc.rev :=
  ⟨rfl, rfl⟩

/-- Each rank cell of the opposite core has the dimension of the original type (II) simplex ... -/
theorem opCell_dim (s : (core.{u} k n).ι) :
    (⟨(core.{u} k n).op.equivII s, rfl⟩ : (opRank.{u} k n).Cell _).dim = s.d :=
  Subcomplex.PairingCore.rankCell_dim (core.{u} k n).op (opRank.{u} k n) s rfl

/-- ... and misses the reversed face. -/
theorem opCell_index (s : (core.{u} k n).ι) :
    (⟨(core.{u} k n).op.equivII s, rfl⟩ : (opRank.{u} k n).Cell _).index = s.index.castSucc.rev :=
  Subcomplex.PairingCore.rankCell_index (core.{u} k n).op (opRank.{u} k n) s rfl

/-- The opposite keeps the ancestral relation. -/
example (s t : (core.{u} k n).ι) :
    (core.{u} k n).op.AncestralRel s t ↔ (core.{u} k n).AncestralRel s t :=
  Subcomplex.PairingCore.op_ancestralRel_iff _ s t

end MathlibExtTest.AlgebraicTopology.SimplicialSet.PairingCoreClients
