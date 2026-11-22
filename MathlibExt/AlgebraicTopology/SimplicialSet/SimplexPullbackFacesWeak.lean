/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.HornPreimageWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexFibrationTransitions
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber

/-!
# Actual simplex transitions give the full original face and horn comparisons

Every nonempty original face is represented by its native finite ordered
vertex set. Its complete original preimage is identified with the SAME
native simplex-pullback source, retaining both projections. Thus genuine
weak transitions of the original simplex diagram imply all full face
comparisons and then the whole original horn-preimage comparison.
No Kan, sharpness, or global weak-equivalence outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet

variable {E B : SSet.{u}}

/-- Actual weak transitions of the SAME original simplex-pullback diagram give
the literal full preimage inclusion of every nonempty original face. -/
theorem simplexPullbackFace_mem_realizationWeakEquivalences (p : E ⟶ B)
    (h : ∀ {s t : SimplexIndex B} (a : s ⟶ t),
      realizationWeakEquivalences ((simplexPullbackDiagram p).map a))
    {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ B) (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    realizationWeakEquivalences ((stdSimplex.face S).preimage (pullback.snd p σ)).ι := by
  classical
  let m := S.card - 1
  have hc : S.card = m + 1 := by
    have hp := Finset.card_pos.mpr hS
    dsimp [m]
    omega
  let e : (Δ[m] : SSet.{u}) ≅ (stdSimplex.face S : SSet.{u}) :=
    stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy S m (S.orderIsoOfFin hc))
  let α : ⦋m⦌ ⟶ ⦋n⦌ := SSet.stdSimplex.preimage (e.hom ≫ (stdSimplex.face S).ι)
  have hα : SSet.stdSimplex.map α = e.hom ≫ (stdSimplex.face S).ι := SSet.stdSimplex.map_preimage _
  let s : SimplexIndex B := CostructuredArrow.mk (SSet.stdSimplex.map α ≫ σ)
  let t : SimplexIndex B := CostructuredArrow.mk σ
  let a : s ⟶ t := CostructuredArrow.homMk α (by rfl)
  let Q : (pullback p σ).Subcomplex := (stdSimplex.face S).preimage (pullback.snd p σ)
  have original := (Subcomplex.preimage_isPullback (stdSimplex.face S) (pullback.snd p σ)).paste_horiz
    (IsPullback.of_hasPullback p σ)
  have square : IsPullback (Q.ι ≫ pullback.fst p σ)
      ((stdSimplex.face S).fromPreimage (pullback.snd p σ) ≫ e.inv) p (SSet.stdSimplex.map α ≫ σ) := by
    apply original.of_iso' (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · rfl
    · simp
    · simp
    · rw [hα]
      simp
  let eQ : (Q : SSet.{u}) ≅ pullback p (SSet.stdSimplex.map α ≫ σ) := square.isoPullback
  have eQfst : eQ.hom ≫ pullback.fst p (SSet.stdSimplex.map α ≫ σ) = Q.ι ≫ pullback.fst p σ :=
    square.isoPullback_hom_fst
  have eQsnd : eQ.hom ≫ pullback.snd p (SSet.stdSimplex.map α ≫ σ) =
      (stdSimplex.face S).fromPreimage (pullback.snd p σ) ≫ e.inv := square.isoPullback_hom_snd
  have comm : eQ.hom ≫ (simplexPullbackDiagram p).map a = Q.ι := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => eQ.hom ≫ f) (simplexPullbackDiagram_map_fst p a)).trans eQfst)
    · calc
        (eQ.hom ≫ (simplexPullbackDiagram p).map a) ≫ pullback.snd p σ =
            eQ.hom ≫ (pullback.snd p (SSet.stdSimplex.map α ≫ σ) ≫ SSet.stdSimplex.map α) :=
          (Category.assoc _ _ _).trans
            (congrArg (fun f => eQ.hom ≫ f) (simplexPullbackDiagram_map_snd p a))
        _ = ((stdSimplex.face S).fromPreimage (pullback.snd p σ) ≫ e.inv) ≫ SSet.stdSimplex.map α :=
          (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ SSet.stdSimplex.map α) eQsnd)
        _ = (stdSimplex.face S).fromPreimage (pullback.snd p σ) ≫ (stdSimplex.face S).ι := by
          rw [hα, Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp]
        _ = Q.ι ≫ pullback.snd p σ := Subcomplex.fromPreimage_ι _ _
  have hw : realizationWeakEquivalences (eQ.hom ≫ (simplexPullbackDiagram p).map a) :=
    realizationWeakEquivalences.comp_mem _ _ (realizationWeakEquivalences.of_isIso _) (h a)
  exact (congrArg (fun f : (Q : SSet.{u}) ⟶ pullback p σ => realizationWeakEquivalences f) comm).mp hw

/-- ALL genuine weak original simplex transitions imply the SAME full horn
preimage map is weak over every original standard simplex and every horn. -/
theorem simplexPullbackHorn_mem_realizationWeakEquivalences (p : E ⟶ B)
    (h : ∀ {s t : SimplexIndex B} (a : s ⟶ t),
      realizationWeakEquivalences ((simplexPullbackDiagram p).map a))
    {n : ℕ} (σ : (Δ[n + 1] : SSet.{u}) ⟶ B) (k : Fin (n + 2)) :
    realizationWeakEquivalences ((horn (n + 1) k).preimage (pullback.snd p σ)).ι :=
  hornPreimage_mem_realizationWeakEquivalences_of_faces (pullback.snd p σ) k
    (simplexPullbackFace_mem_realizationWeakEquivalences p h σ)

end SSet
