/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.PairingCellReader
import MathlibExt.AlgebraicTopology.SimplicialSet.PairingCoreTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexVertexCoverage
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-!
# The original upper-endpoint coordinate and scalar-boundary pairing core

Opposite transports the actual standard interval endpoint / scalar
boundary pairing through its original simplex product isomorphisms.
The original dimension, missing index and full grid simplex are kept.
At the final missing index its original last edge changes only the
interval coordinate at the unchanged final scalar vertex.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

/-- The actual original upper interval endpoint / scalar boundary product pairing keeps its native opposite-core
source and every original simplex map. -/
def rootCoordinateEndpointCore (d : ℕ) :
    (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).PairingCore :=
  (prodStdSimplex.pairingCore.{u} (0 : Fin 1) d).op.ofIso
    (((stdSimplex.opIso _).symm ⊗ᵢ (stdSimplex.opIso _).symm) ≪≫
      Functor.Monoidal.μIso opFunctor _ _) (by
        dsimp
        rw [Subcomplex.preimage_comp, Subcomplex.preimage_op_unionProd,
          Subcomplex.preimage_unionProd, op_boundary, op_horn, Fin.rev_zero]
        rfl)

local instance rootCoordinateEndpointCoreRegular (d : ℕ) : (rootCoordinateEndpointCore.{u} d).IsRegular := by
  dsimp only [rootCoordinateEndpointCore]
  infer_instance

local instance rootCoordinateEndpointPairingRegular (d : ℕ) : (rootCoordinateEndpointCore.{u} d).pairing.IsRegular :=
  (Subcomplex.PairingCore.isRegular_pairing_iff _).mpr inferInstance

/-- The native opposite coordinate core retains exactly the actual original cell dimension. -/
theorem rootCoordinateEndpointCore_dim (d : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d) :
    (rootCoordinateEndpointCore d).dim s = s.d := rfl

/-- The actual missing index is precisely the original reversed index, without a replacement rank or simplex. -/
theorem rootCoordinateEndpointCore_index (d : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d) :
    (rootCoordinateEndpointCore d).index s = s.index.castSucc.rev := rfl

/-- Every whole actual interval grid coordinate is its unchanged original opposite coordinate. -/
theorem rootCoordinateEndpointCore_grid_fst (d : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d)
    (i : Fin (s.d + 2)) :
    ((rootCoordinateEndpointCore d).simplex s).1 i =
      (((prodStdSimplex.pairingCore (0 : Fin 1) d).simplex s).1 i.rev).rev := rfl

/-- Every whole actual scalar grid coordinate is its unchanged original opposite scalar coordinate. -/
theorem rootCoordinateEndpointCore_grid_snd (d : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d)
    (i : Fin (s.d + 2)) :
    ((rootCoordinateEndpointCore d).simplex s).2 i =
      (((prodStdSimplex.pairingCore (0 : Fin 1) d).simplex s).2 i.rev).rev := rfl

/-- Every original scalar parameter vertex is in the actual product source when that parameter has positive
dimension. -/
theorem rootCoordinateEndpointSource_vertex_mem (d : ℕ) (hd : 0 < d)
    (x : ((Δ[1] : SSet.{u}) ⊗ Δ[d]) _⦋0⦌) :
    x ∈ (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).obj (op ⦋0⦌) := by
  apply (Subcomplex.mem_unionProd_iff _ _ x).mpr
  apply Or.inl
  rw [boundary_obj_eq_univ 0 d hd]
  exact Set.mem_univ _

/-- Original vertex coverage gives the genuine positive dimension of every actual relative core cell. -/
theorem rootCoordinateEndpointCore_one_le_dim (d : ℕ) (hd : 0 < d)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d) : 1 ≤ s.d :=
  Subcomplex.N.one_le_dim_of_vertices (rootCoordinateEndpointSource_vertex_mem d hd)
    ((rootCoordinateEndpointCore d).type₂ s)

/-- The same original scalar grid begins at its actual original scalar zero vertex. -/
theorem rootCoordinateEndpointOriginal_scalar_zero (d : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d) :
    ((s.x.cast s.hd).simplex.2) (0 : Fin (s.d + 2)) = 0 := by
  obtain ⟨i, hi⟩ := prodStdSimplex.pairingCore.mem_range_right s.x s.hd (0 : Fin (d + 1))
  exact le_antisymm
    ((stdSimplex.monotone_apply (s.x.cast s.hd).simplex.2 (Fin.zero_le i)).trans_eq hi)
    (Fin.zero_le _)

/-- A final-index core cell's original last two grid vertices change only the original interval coordinate at the
original last scalar vertex. -/
theorem rootCoordinateEndpointCore_final_grid (d : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d) (hs : s.index = 0) :
    (((rootCoordinateEndpointCore d).simplex s).1 (Fin.last s.d).castSucc,
      ((rootCoordinateEndpointCore d).simplex s).2 (Fin.last s.d).castSucc) = (0, Fin.last d) ∧
    (((rootCoordinateEndpointCore d).simplex s).1 (Fin.last (s.d + 1)),
      ((rootCoordinateEndpointCore d).simplex s).2 (Fin.last (s.d + 1))) = (1, Fin.last d) := by
  have hr : (Fin.last s.d).castSucc.rev = (0 : Fin (s.d + 1)).succ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_last, Fin.val_succ, Fin.val_zero]
    omega
  have hf₀ : (s.x.cast s.hd).simplex.1 (0 : Fin (s.d + 2)) = 0 := by
    simpa only [hs, Fin.castSucc_zero] using s.isIndex.simplex_fst_castSucc
  have hf₁ : (s.x.cast s.hd).simplex.1 (0 : Fin (s.d + 1)).succ = 1 := by
    have h : (s.x.cast s.hd).simplex.1 (0 : Fin (s.d + 1)).succ = (0 : Fin 1).succ := by
      simpa only [hs] using s.isIndex.simplex_fst_succ
    exact h.trans (show (0 : Fin 1).succ = (1 : Fin 2) from by decide)
  have ht₁ : (s.x.cast s.hd).simplex.2 (0 : Fin (s.d + 1)).succ = 0 := by
    have h := s.isIndex.simplex_snd_succ
    simpa only [hs, Fin.castSucc_zero, rootCoordinateEndpointOriginal_scalar_zero d s] using h
  constructor
  · apply Prod.ext
    · rw [rootCoordinateEndpointCore_grid_fst, hr]
      exact (congrArg Fin.rev hf₁).trans (show (1 : Fin 2).rev = 0 from by decide)
    · rw [rootCoordinateEndpointCore_grid_snd, hr]
      exact (congrArg Fin.rev ht₁).trans (Fin.rev_zero _)
  · apply Prod.ext
    · rw [rootCoordinateEndpointCore_grid_fst, Fin.rev_last]
      exact (congrArg Fin.rev hf₀).trans (show (0 : Fin 2).rev = 1 from by decide)
    · rw [rootCoordinateEndpointCore_grid_snd, Fin.rev_last]
      exact (congrArg Fin.rev (rootCoordinateEndpointOriginal_scalar_zero d s)).trans (Fin.rev_zero _)

end SSet.Marked.CoherentWeight
