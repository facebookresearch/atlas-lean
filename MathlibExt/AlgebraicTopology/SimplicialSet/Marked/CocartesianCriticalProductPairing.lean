/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ControlledPairingLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellMarkingCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.PairingCellReader
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexVertexCoverage
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-!
# The actual cocartesian critical-horn product pairing

Use the original native regular pairing of the critical initial horn and
an arbitrary scalar boundary. Every non-inner attaching horn has its
actual first edge in the original marked critical edge. The other scalar
factor is maximally marked. Original mark coverage gives every vertex
and every later marked edge at the source stage. No Kan hypothesis on
the parameter or base and no marked-model outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

local instance criticalPairingRegular (m n : ℕ) :
    (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing.IsRegular :=
  (Subcomplex.PairingCore.isRegular_pairing_iff _).mpr inferInstance

/-- Every original product mark lies in the original critical-horn/boundary source. -/
theorem cocartesianCriticalProduct_marks_mem (m n : ℕ)
    (e : (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).toSSet _⦋1⦌)
    (he : e ∈ (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking) :
    e ∈ (Subcomplex.unionProd (horn.{u} (m + 2) (0 : Fin (m + 3))) (boundary.{u} n)).obj (op ⦋1⦌) := by
  obtain ⟨a, ha, h⟩ := cocartesianCriticalCell_markingSurjective m e.1 he.1
  have hA : e.1 ∈ (horn.{u} (m + 2) (0 : Fin (m + 3))).obj (op ⦋1⦌) := by
    change a.val = e.1 at h
    exact h ▸ a.property
  exact (Subcomplex.mem_unionProd_iff _ _ e).mpr (Or.inr hA)

private theorem exists_initial_critical (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 2)) (hi : i = 0) :
    ∃ e : (horn.{u} (n + 1) i : SSet.{u}) _⦋1⦌,
      (horn.{u} (n + 1) i).ι.app (op ⦋1⦌) e =
        stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _) := by
  subst i
  refine ⟨⟨stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _), ?_⟩, rfl⟩
  rw [mem_horn_iff_notMem_range]
  refine ⟨⟨2, by omega⟩, ?_, ?_⟩
  · intro h
    have h' : (2 : ℕ) = 0 := by simpa using congrArg Fin.val h
    omega
  · rintro ⟨k, hk⟩
    fin_cases k
    · change (0 : Fin (n + 2)) = ⟨2, by omega⟩ at hk
      have h' := congrArg Fin.val hk
      simp only [Fin.val_zero] at h'
      omega
    · change (1 : Fin (n + 2)) = ⟨2, by omega⟩ at hk
      have h' := congrArg Fin.val hk
      change 1 % (n + 2) = 2 at h'
      rw [Nat.mod_eq_of_lt (by omega)] at h'
      omega

private theorem core_initial_edge {m n : ℕ}
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n)
    (hs : s.index = 0) :
    ((yonedaEquiv.symm ((prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).simplex s)).app
      (op ⦋1⦌) (stdSimplex.edge (s.d + 1) 0 ((0 : Fin (s.d + 1)).succ) (Fin.zero_le _))).1 =
      (horn.{u} (m + 2) (0 : Fin (m + 3))).ι.app (op ⦋1⦌) (leftHornEdgeSimplex.{u} m) := by
  apply stdSimplex.ext
  intro k
  fin_cases k
  · change (s.x.cast s.hd).simplex.1 0 = 0
    simpa only [hs, Fin.castSucc_zero] using s.isIndex.simplex_fst_castSucc
  · change (s.x.cast s.hd).simplex.1 ((0 : Fin (s.d + 1)).succ) = ((0 : Fin (m + 2)).succ)
    simpa only [hs] using s.isIndex.simplex_fst_succ

private theorem criticalCell_first_edge_marked (m n : ℕ)
    (j : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n)
    (ht : (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing.rankFunction.rank
      ((prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).equivII s) = j)
    (hz : (⟨(prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).equivII s, ht⟩ :
      (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing.rankFunction.Cell j).index = 0) :
    let c : (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing.rankFunction.Cell j :=
      ⟨(prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).equivII s, ht⟩
    c.map.app (op ⦋1⦌)
      (stdSimplex.edge (c.dim + 1) 0 ((0 : Fin (c.dim + 1)).succ) (Fin.zero_le _)) ∈
      (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking := by
  let h := prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n
  let f := h.pairing.rankFunction
  let c : f.Cell j := ⟨h.equivII s, ht⟩
  have hidx : c.index.val = s.index.val := h.rankCell_index_val f s ht
  have hsidx : s.index = 0 := by
    apply Fin.ext
    change s.index.val = 0
    exact hidx.symm.trans (show c.index.val = 0 from congrArg Fin.val hz)
  have hcmap : c.map = yonedaEquiv.symm (h.simplex s) := by
    have hmap := h.rankCell_map f s ht
    change c.map = 𝟙 _ ≫ yonedaEquiv.symm (h.simplex s) at hmap
    exact hmap.trans (Category.id_comp _)
  have hcritical := (congrArg (fun z : (Δ[s.d + 1] : SSet.{u}) ⟶ (Δ[m + 2] : SSet.{u}) ⊗ Δ[n] =>
      (z.app (op ⦋1⦌) (stdSimplex.edge (s.d + 1) 0 ((0 : Fin (s.d + 1)).succ) (Fin.zero_le _))).1) hcmap).trans
    (core_initial_edge s hsidx)
  exact ⟨Or.inr hcritical, Set.mem_univ _⟩

private theorem criticalCell_horn_edge_mem (m n : ℕ)
    (j : ℕ) (c : (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing.rankFunction.Cell j)
    (e : c.horn.toSSet _⦋1⦌)
    (he : c.horn.ι.app (op ⦋1⦌) e =
      stdSimplex.edge (c.dim + 1) 0 ((0 : Fin (c.dim + 1)).succ) (Fin.zero_le _))
    (hm : c.map.app (op ⦋1⦌)
      (stdSimplex.edge (c.dim + 1) 0 ((0 : Fin (c.dim + 1)).succ) (Fin.zero_le _)) ∈
      (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking) :
    c.mapHorn.app (op ⦋1⦌) e ∈
      (comap (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
        ((prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing.rankFunction.filtration j).ι).marking := by
  let f := (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing.rankFunction
  have hr : (f.filtration j).ι.app (op ⦋1⦌) (c.mapHorn.app (op ⦋1⦌) e) =
      c.map.app (op ⦋1⦌) (stdSimplex.edge (c.dim + 1) 0 ((0 : Fin (c.dim + 1)).succ) (Fin.zero_le _)) :=
    (Subcomplex.Pairing.RankFunction.Cell.mapHorn_app_ι f c e).trans
      (congrArg (c.map.app (op ⦋1⦌)) he)
  change (f.filtration j).ι.app (op ⦋1⦌) (c.mapHorn.app (op ⦋1⦌) e) ∈
    (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))).marking
  exact hr.symm ▸ hm

/-- The original regular critical-horn product pairing satisfies the exact source-index and
  marked-critical-edge conditions. -/
theorem cocartesianCriticalProduct_pairing_controlled (m n : ℕ) :
    @CocartesianControlledPairing.{u}
      (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
      (Subcomplex.unionProd (horn.{u} (m + 2) (0 : Fin (m + 3))) (boundary.{u} n))
      (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing (criticalPairingRegular m n) := by
  let ambient := prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))
  let A := Subcomplex.unionProd (horn.{u} (m + 2) (0 : Fin (m + 3))) (boundary.{u} n)
  let h := prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n
  let f := h.pairing.rankFunction
  have hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌) :=
    cocartesianCriticalProduct_marks_mem m n
  intro j c
  rcases c with ⟨t, ht⟩
  obtain ⟨s, rfl⟩ := h.equivII.surjective t
  let c : f.Cell j := ⟨h.equivII s, ht⟩
  have hdim : c.dim = s.d := h.rankCell_dim f s ht
  have hidx : c.index.val = s.index.val := h.rankCell_index_val f s ht
  have hlast : c.index < Fin.last (c.dim + 1) := by
    rw [Fin.lt_def, Fin.val_last]
    have hs := s.index.isLt
    omega
  by_cases hz : c.index = 0
  · right
    have hd : 1 ≤ c.dim :=
      Subcomplex.N.one_le_dim_of_vertices (vertices_mem_of_marks_mem ambient A hmarks) c.s.val
    obtain ⟨e, he⟩ := exists_initial_critical c.dim hd c.index hz
    exact ⟨hd, hz, e, he, criticalCell_horn_edge_mem m n j c e he
      (criticalCell_first_edge_marked m n j s ht hz)⟩
  · left
    refine ⟨?_, hlast⟩
    rw [Fin.lt_def]
    have hval : c.index.val ≠ 0 := by
      intro hh
      exact hz (Fin.ext hh)
    exact Nat.pos_of_ne_zero hval

/-- The whole original marked critical-horn product source lifts against the supplied intrinsic cocartesian
  projection. -/
theorem cocartesianCriticalProduct_lifting (m n : ℕ) {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty
      (comapHom (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
        (Subcomplex.unionProd (horn.{u} (m + 2) (0 : Fin (m + 3))) (boundary.{u} n)).ι)
      (cocartesianProjection p) :=
  @cocartesianControlledPairing_lifting.{u}
    (prod (cocartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
    (Subcomplex.unionProd (horn.{u} (m + 2) (0 : Fin (m + 3))) (boundary.{u} n))
    (prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n).pairing
    (criticalPairingRegular m n)
    (cocartesianCriticalProduct_marks_mem m n) (cocartesianCriticalProduct_pairing_controlled m n) E B p
      inferInstance inferInstance

end SSet.Marked
