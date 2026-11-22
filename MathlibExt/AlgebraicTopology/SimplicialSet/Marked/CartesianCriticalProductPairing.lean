/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ControlledCartesianPairingLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellMarkingCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.PairingCellReader
import MathlibExt.AlgebraicTopology.SimplicialSet.PairingCoreTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexVertexCoverage
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-!
# The original Cartesian critical-horn product pairing

Opposite transports the original indexed critical-horn pairing through
the native standard-simplex isomorphisms. It preserves every dimension
and reverses each actual missing-face index. The only final outer horns
have the original marked final critical edge. No Kan assumption on the
parameter or base, changed rank, or marked-model outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The same original critical product, oppositely indexed through the native whole standard-simplex comparison. -/
def cartesianCriticalProductCore (m n : ℕ) :
    (Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n)).PairingCore :=
  (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).op.ofIso
    (((stdSimplex.opIso _).symm ⊗ᵢ (stdSimplex.opIso _).symm) ≪≫
      Functor.Monoidal.μIso opFunctor _ _) (by
        dsimp
        rw [Subcomplex.preimage_comp, Subcomplex.preimage_op_unionProd,
          Subcomplex.preimage_unionProd, op_boundary, op_horn, Fin.rev_zero])

local instance criticalFinalCoreRegular (m n : ℕ) : (cartesianCriticalProductCore.{u} m n).IsRegular := by
  dsimp only [cartesianCriticalProductCore]
  infer_instance

local instance criticalFinalPairingRegular (m n : ℕ) : (cartesianCriticalProductCore.{u} m n).pairing.IsRegular :=
  (Subcomplex.PairingCore.isRegular_pairing_iff _).mpr inferInstance

/-- The opposite core retains precisely the original type-II dimension. -/
@[simp]
theorem cartesianCriticalProductCore_dim (m n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n) :
    (cartesianCriticalProductCore m n).dim s = s.d := rfl

/-- Its literal missing-face index is the reversed original index, with no new pairing rank. -/
@[simp]
theorem cartesianCriticalProductCore_index (m n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n) :
    (cartesianCriticalProductCore m n).index s = s.index.castSucc.rev := rfl

private theorem opposite_grid_fst (m n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n) (k : Fin (s.d + 2)) :
    ((cartesianCriticalProductCore m n).simplex s).1 k =
      (((prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).simplex s).1 k.rev).rev := rfl

/-- Every actual original product mark is already in the supplied critical-horn/boundary source. -/
theorem cartesianCriticalProduct_marks_mem (m n : ℕ)
    (e : (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).toSSet _⦋1⦌)
    (he : e ∈ (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking) :
    e ∈ (Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n)).obj (op ⦋1⦌) := by
  obtain ⟨a, ha, h⟩ := cartesianCriticalCell_markingSurjective m e.1 he.1
  have hA : e.1 ∈ (horn.{u} (m + 2) (Fin.last (m + 2))).obj (op ⦋1⦌) := by
    change a.val = e.1 at h
    exact h ▸ a.property
  exact (Subcomplex.mem_unionProd_iff _ _ e).mpr (Or.inr hA)

private theorem exists_final_critical (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 2))
    (hi : i = Fin.last (d + 1)) :
    ∃ e : (horn.{u} (d + 1) i : SSet.{u}) _⦋1⦌,
      (horn.{u} (d + 1) i).ι.app (op ⦋1⦌) e =
        stdSimplex.edge (d + 1) (Fin.last d).castSucc (Fin.last (d + 1)) (Fin.le_last _) := by
  subst i
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  exact ⟨rightHornEdgeSimplex.{u} m, rfl⟩

private theorem core_final_edge {m n : ℕ}
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n)
    (hs : s.index = 0) :
    ((yonedaEquiv.symm ((cartesianCriticalProductCore.{u} m n).simplex s)).app
      (op ⦋1⦌) (stdSimplex.edge (s.d + 1) (Fin.last s.d).castSucc (Fin.last (s.d + 1)) (Fin.le_last _))).1 =
      (horn.{u} (m + 2) (Fin.last (m + 2))).ι.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} m) := by
  apply stdSimplex.ext
  intro k
  fin_cases k
  · change ((cartesianCriticalProductCore.{u} m n).simplex s).1 (Fin.last s.d).castSucc =
      (Fin.last (m + 1)).castSucc
    rw [opposite_grid_fst]
    have hr : (Fin.last s.d).castSucc.rev = (0 : Fin (s.d + 1)).succ := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_last, Fin.val_succ, Fin.val_zero]
      omega
    rw [hr]
    change ((s.x.cast s.hd).simplex.1 ((0 : Fin (s.d + 1)).succ)).rev = (Fin.last (m + 1)).castSucc
    have h : (s.x.cast s.hd).simplex.1 ((0 : Fin (s.d + 1)).succ) = (0 : Fin (m + 2)).succ := by
      simpa only [hs] using s.isIndex.simplex_fst_succ
    refine (congrArg Fin.rev h).trans ?_
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.val_last]
    omega
  · change ((cartesianCriticalProductCore.{u} m n).simplex s).1 (Fin.last (s.d + 1)) =
      Fin.last (m + 2)
    rw [opposite_grid_fst, Fin.rev_last]
    change ((s.x.cast s.hd).simplex.1 0).rev = Fin.last (m + 2)
    have h : (s.x.cast s.hd).simplex.1 0 = 0 := by
      simpa only [hs, Fin.castSucc_zero] using s.isIndex.simplex_fst_castSucc
    exact (congrArg Fin.rev h).trans (Fin.rev_zero _)

private theorem criticalFinalCell_last_edge_marked (m n : ℕ)
    (j : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n)
    (ht : (cartesianCriticalProductCore.{u} m n).pairing.rankFunction.rank
      ((cartesianCriticalProductCore.{u} m n).equivII s) = j)
    (hz : (⟨(cartesianCriticalProductCore.{u} m n).equivII s, ht⟩ :
      (cartesianCriticalProductCore.{u} m n).pairing.rankFunction.Cell j).index = Fin.last (s.d + 1)) :
    let c : (cartesianCriticalProductCore.{u} m n).pairing.rankFunction.Cell j :=
      ⟨(cartesianCriticalProductCore.{u} m n).equivII s, ht⟩
    c.map.app (op ⦋1⦌)
      (stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _)) ∈
      (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking := by
  let h := cartesianCriticalProductCore.{u} m n
  let f := h.pairing.rankFunction
  let c : f.Cell j := ⟨h.equivII s, ht⟩
  have hidx : c.index = s.index.castSucc.rev := h.rankCell_index f s ht
  have hsidx : s.index = 0 := by
    have hi : s.index.castSucc.rev = Fin.last (s.d + 1) := hidx.symm.trans hz
    have hh := congrArg Fin.rev hi
    simpa only [Fin.rev_rev, Fin.rev_last, Fin.castSucc_eq_zero_iff] using hh
  have hcmap : c.map = yonedaEquiv.symm (h.simplex s) := by
    have hmap := h.rankCell_map f s ht
    change c.map = 𝟙 _ ≫ yonedaEquiv.symm (h.simplex s) at hmap
    exact hmap.trans (Category.id_comp _)
  have hcritical := (congrArg (fun z : (Δ[s.d + 1] : SSet.{u}) ⟶ (Δ[m + 2] : SSet.{u}) ⊗ Δ[n] =>
      (z.app (op ⦋1⦌) (stdSimplex.edge (s.d + 1) (Fin.last s.d).castSucc (Fin.last (s.d + 1)) (Fin.le_last
        _))).1) hcmap).trans
    (core_final_edge s hsidx)
  exact ⟨Or.inr hcritical, Set.mem_univ _⟩

private theorem criticalFinalCell_horn_edge_mem (m n : ℕ)
    (j : ℕ) (c : (cartesianCriticalProductCore.{u} m n).pairing.rankFunction.Cell j)
    (e : c.horn.toSSet _⦋1⦌)
    (he : c.horn.ι.app (op ⦋1⦌) e =
      stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _))
    (hm : c.map.app (op ⦋1⦌)
      (stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _)) ∈
      (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking) :
    c.mapHorn.app (op ⦋1⦌) e ∈
      (comap (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
        ((cartesianCriticalProductCore.{u} m n).pairing.rankFunction.filtration j).ι).marking := by
  let f := (cartesianCriticalProductCore.{u} m n).pairing.rankFunction
  have hr : (f.filtration j).ι.app (op ⦋1⦌) (c.mapHorn.app (op ⦋1⦌) e) =
      c.map.app (op ⦋1⦌) (stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1))
        (Fin.le_last _)) :=
    (Subcomplex.Pairing.RankFunction.Cell.mapHorn_app_ι f c e).trans
      (congrArg (c.map.app (op ⦋1⦌)) he)
  change (f.filtration j).ι.app (op ⦋1⦌) (c.mapHorn.app (op ⦋1⦌) e) ∈
    (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking
  exact hr.symm ▸ hm

/-- The oppositely indexed original product pairing has only inner horns or final horns with their actual
  original critical edge marked at the old stage. -/
theorem cartesianCriticalProduct_pairing_controlled (m n : ℕ) :
    @CartesianControlledPairing.{u}
      (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
      (Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n))
      (cartesianCriticalProductCore.{u} m n).pairing (criticalFinalPairingRegular m n) := by
  let ambient := prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))
  let A := Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n)
  let h := cartesianCriticalProductCore.{u} m n
  let f := h.pairing.rankFunction
  have hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌) :=
    cartesianCriticalProduct_marks_mem m n
  intro j c
  rcases c with ⟨t, ht⟩
  obtain ⟨s, rfl⟩ := h.equivII.surjective t
  let c : f.Cell j := ⟨h.equivII s, ht⟩
  have hidx : c.index.val = s.index.castSucc.rev.val := h.rankCell_index_val f s ht
  have hpos : 0 < c.index := by
    change 0 < c.index.val
    simp only [Fin.val_rev, Fin.val_castSucc] at hidx
    have hs := s.index.isLt
    omega
  by_cases hz : c.index = Fin.last (c.dim + 1)
  · right
    have hd : 1 ≤ c.dim :=
      Subcomplex.N.one_le_dim_of_vertices (vertices_mem_of_marks_mem ambient A hmarks) c.s.val
    obtain ⟨e, he⟩ := exists_final_critical c.dim hd c.index hz
    exact ⟨hd, hz, e, he, criticalFinalCell_horn_edge_mem m n j c e he
      (criticalFinalCell_last_edge_marked m n j s ht hz)⟩
  · left
    exact ⟨hpos, lt_of_le_of_ne (Fin.le_last _) hz⟩

/-- The complete original marked final-critical-horn product source lifts against its supplied intrinsic
  Cartesian projection. -/
theorem cartesianCriticalProduct_lifting (m n : ℕ) {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty
      (comapHom (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
        (Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n)).ι)
      (cartesianProjection p) :=
  @cartesianControlledPairing_lifting.{u}
    (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
    (Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n))
    (cartesianCriticalProductCore.{u} m n).pairing (criticalFinalPairingRegular m n)
    (cartesianCriticalProduct_marks_mem m n) (cartesianCriticalProduct_pairing_controlled m n) E B p
      inferInstance inferInstance

end SSet.Marked
