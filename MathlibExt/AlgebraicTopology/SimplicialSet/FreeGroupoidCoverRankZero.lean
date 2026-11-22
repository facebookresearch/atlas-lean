/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverRankCoverage

/-!
# The SAME actual original rank-zero cover graph is the native root point

Every original rank-zero vertex is the SAME native identity-path root.
There are no original generating arrows between rank-zero vertices.
Full original graph-word recovery gives the actual point isomorphism,
retaining every native ordinal coefficient and root inclusion.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in the native root stage. -/
private local instance coverQuiverForRootStage : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The SAME native identity-path cover root gives the actual original simplicial point map. -/
def coverRootPoint : (Δ[0] : SSet.{max u v}) ⟶ nerve (Paths (CoverVertex V z)) :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₀ (C := Paths (CoverVertex V z)) (coverRoot V z))

/-- Every original point coefficient retains the SAME complete native constant root word. -/
lemma coverRootPoint_app (n : ℕ) (c : (Δ[0] : SSet.{max u v}) _⦋n⦌) :
    (coverRootPoint V z).app (op ⦋n⦌) c =
      (Functor.const (Fin (n + 1)) (C := Paths (CoverVertex V z))).obj (coverRoot V z : Paths (CoverVertex V z)) := by
  apply Functor.hext (D := Paths (CoverVertex V z)) (fun _ => rfl)
  intro i j f
  rfl

/-- Every original native root-point coefficient lands in the SAME rank-zero graph. -/
lemma coverRootPoint_range_le_zero : SSet.Subcomplex.range (coverRootPoint V z) ≤ coverRankStage V z 0 := by
  intro q w hw
  obtain ⟨c, rfl⟩ := hw
  rcases q with ⟨⟨n⟩⟩
  rw [coverRootPoint_app]
  apply (mem_coverRankStage V z 0 (op ⦋n⦌) _).mpr
  constructor
  · change (0 : ℕ) ≤ 1
    omega
  · intro i
    exact (CoverVertex.rank_eq_zero_iff V z (coverRoot V z)).mpr rfl |>.le

/-- Every original rank-zero word is the SAME full native constant root word. -/
lemma coverRankZero_word (n : ℕ) (w : (nerve (Paths (CoverVertex V z))) _⦋n⦌)
    (hw : w ∈ (coverRankStage V z 0).obj (op ⦋n⦌)) :
    w = (Functor.const (Fin (n + 1)) (C := Paths (CoverVertex V z))).obj (coverRoot V z : Paths (CoverVertex V z)) := by
  change Fin (n + 1) ⥤ Paths (CoverVertex V z) at w
  have hs := (mem_coverRankStage V z 0 (op ⦋n⦌) w).mp hw
  have hzero : (CategoryTheory.FreePathNerveCoordinates.totalPath (CoverVertex V z) n w).length = 0 := by
    have hl : (CategoryTheory.FreePathNerveCoordinates.totalPath (CoverVertex V z) n w).length ≤ 1 := hs.1
    by_contra hn
    have hone : (CategoryTheory.FreePathNerveCoordinates.totalPath (CoverVertex V z) n w).length = 1 := by omega
    obtain ⟨f, c, hc⟩ := CategoryTheory.FreePathNerveCoordinates.original_graph_word_generator (CoverVertex V z) n w
      hone
    have hsource := hs.2 0
    have htarget := hs.2 (Fin.last n)
    rcases coverArrow_rank_step V z f with h | h <;> omega
  have hc := CategoryTheory.FreePathNerveCoordinates.original_graph_word_constant (CoverVertex V z) n w hzero
  have hr : w.obj 0 = coverRoot V z := (CoverVertex.rank_eq_zero_iff V z (w.obj 0)).mp (Nat.eq_zero_of_le_zero (hs.2 0))
  exact hc.trans (congrArg (fun a : Paths (CoverVertex V z) => (Functor.const (Fin (n + 1)) (C := Paths (CoverVertex
    V z))).obj a) hr)

/-- The actual original root point factors into the SAME native rank-zero graph. -/
def coverRootToZero : (Δ[0] : SSet.{max u v}) ⟶ (coverRankStage V z 0 : SSet.{max u v}) :=
  SSet.Subcomplex.lift (coverRootPoint V z) (coverRootPoint_range_le_zero V z)

/-- The original root-stage inclusion retains the SAME actual native point map. -/
lemma coverRootToZero_ι : coverRootToZero V z ≫ (coverRankStage V z 0).ι = coverRootPoint V z :=
  SSet.Subcomplex.lift_ι _ _

/-- The SAME actual root-point comparison is an isomorphism, with all original coefficients retained. -/
instance coverRootToZero_isIso : IsIso (coverRootToZero V z) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  constructor
  · intro c d _
    rcases q with ⟨⟨n⟩⟩
    apply SSet.stdSimplex.ext c d
    intro i
    apply Fin.ext
    have hc := (c i).isLt
    have hd := (d i).isLt
    change (c i).val < 1 at hc
    change (d i).val < 1 at hd
    omega
  · intro w
    rcases q with ⟨⟨n⟩⟩
    let c : (Δ[0] : SSet.{max u v}) _⦋n⦌ := SSet.stdSimplex.objMk (OrderHom.const (Fin (n + 1)) (0 : Fin 1))
    refine ⟨c, Subtype.ext ?_⟩
    exact (coverRootPoint_app V z n c).trans (coverRankZero_word V z n w.val w.property).symm

end Quiver.FreeGroupoid.OriginalWords
