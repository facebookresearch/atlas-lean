/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpSimplexCriterion
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Descent of sharpness along epimorphic base maps

Sharpness of maps of simplicial sets descends along an epimorphism of bases. For any supplied pullback square, sharpness of the pulled-back map implies sharpness of the original map, by lifting each simplex of the base and transporting its full operator comparisons.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.SharpSaturation

private theorem exists_simplexLift {E Y : SSet.{u}} (e : E ⟶ Y) [Epi e]
    (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) :
    ∃ b' : (Δ[n] : SSet.{u}) ⟶ E, b' ≫ e = b := by
  have he : Epi (e.app (Opposite.op ⦋n⦌)) := inferInstance
  obtain ⟨z, hz⟩ := CategoryTheory.surjective_of_epi
    (e.app (Opposite.op ⦋n⦌)) (SSet.yonedaEquiv b)
  refine ⟨SSet.yonedaEquiv.symm z, ?_⟩
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] using hz

private theorem pastedSquare {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) {n : ℕ} (b' : (Δ[n] : SSet.{u}) ⟶ E)
    (b : (Δ[n] : SSet.{u}) ⟶ Y) (hb : b' ≫ e = b) :
    IsPullback (pullback.fst q b' ≫ r) (pullback.snd q b') p b := by
  simpa only [hb] using (IsPullback.of_hasPullback q b').paste_horiz H

private def liftedPullbackIso {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) {n : ℕ} (b' : (Δ[n] : SSet.{u}) ⟶ E)
    (b : (Δ[n] : SSet.{u}) ⟶ Y) (hb : b' ≫ e = b) :
    pullback q b' ≅ pullback p b :=
  (pastedSquare H b' b hb).isoPullback

private theorem liftedPullbackIso_hom_fst {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) {n : ℕ} (b' : (Δ[n] : SSet.{u}) ⟶ E)
    (b : (Δ[n] : SSet.{u}) ⟶ Y) (hb : b' ≫ e = b) :
    (liftedPullbackIso H b' b hb).hom ≫ pullback.fst p b =
      pullback.fst q b' ≫ r :=
  (pastedSquare H b' b hb).isoPullback_hom_fst

private theorem liftedPullbackIso_hom_snd {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) {n : ℕ} (b' : (Δ[n] : SSet.{u}) ⟶ E)
    (b : (Δ[n] : SSet.{u}) ⟶ Y) (hb : b' ≫ e = b) :
    (liftedPullbackIso H b' b hb).hom ≫ pullback.snd p b = pullback.snd q b' :=
  (pastedSquare H b' b hb).isoPullback_hom_snd

private def liftedComparisonArrowIso {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) {n m : ℕ}
    (b' : (Δ[n] : SSet.{u}) ⟶ E) (b : (Δ[n] : SSet.{u}) ⟶ Y)
    (hb : b' ≫ e = b) (δ : ⦋m⦌ ⟶ ⦋n⦌) :
    Arrow.mk (pullback.map q (SSet.stdSimplex.map δ ≫ b') q b'
      (𝟙 P) (SSet.stdSimplex.map δ) (𝟙 E) (by simp) (by simp)) ≅
    Arrow.mk (pullback.map p (SSet.stdSimplex.map δ ≫ b) p b
      (𝟙 X) (SSet.stdSimplex.map δ) (𝟙 Y) (by simp) (by simp)) :=
  Arrow.isoMk
    (liftedPullbackIso H (SSet.stdSimplex.map δ ≫ b') (SSet.stdSimplex.map δ ≫ b)
      (by simp only [Category.assoc, hb]))
    (liftedPullbackIso H b' b hb)
    (by
      change (liftedPullbackIso H (SSet.stdSimplex.map δ ≫ b') (SSet.stdSimplex.map δ ≫ b)
          (by simp only [Category.assoc, hb])).hom ≫
        pullback.map p (SSet.stdSimplex.map δ ≫ b) p b
          (𝟙 X) (SSet.stdSimplex.map δ) (𝟙 Y) (by simp) (by simp) =
        pullback.map q (SSet.stdSimplex.map δ ≫ b') q b'
          (𝟙 P) (SSet.stdSimplex.map δ) (𝟙 E) (by simp) (by simp) ≫
            (liftedPullbackIso H b' b hb).hom
      apply pullback.hom_ext
      · simp [Category.assoc, pullback.map, liftedPullbackIso_hom_fst]
      · simp only [Category.assoc, pullback.map, pullback.lift_snd,
          liftedPullbackIso_hom_snd]
        simpa only [Category.assoc] using congrArg
          (fun f : pullback q (SSet.stdSimplex.map δ ≫ b') ⟶ (Δ[m] : SSet.{u}) =>
            f ≫ SSet.stdSimplex.map δ)
          (liftedPullbackIso_hom_snd H (SSet.stdSimplex.map δ ≫ b')
            (SSet.stdSimplex.map δ ≫ b) (by simp only [Category.assoc, hb])))

private theorem allSimplexComparisons_of_epi_pullback {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) [Epi e] (hq : allSimplexComparisons q) :
    allSimplexComparisons p := by
  classical
  let lift (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) : (Δ[n] : SSet.{u}) ⟶ E :=
    Classical.choose (exists_simplexLift e n b)
  have lift_eq (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) : lift n b ≫ e = b :=
    Classical.choose_spec (exists_simplexLift e n b)
  intro n m b δ
  exact (realizationWeakEquivalences.arrow_mk_iso_iff
    (liftedComparisonArrowIso H (lift n b) b (lift_eq n b) δ)).1 (hq n m (lift n b) δ)

/-- Rezk5.1 P4 for the original arbitrary pullback square: sharpness descends
along an epi of scalar bases without epi weakness or a base Kan condition. -/
theorem sharp_of_epi_pullback {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) [Epi e] (hq : SharpComparisonDraft.Sharp q) :
    SharpComparisonDraft.Sharp p :=
  (sharp_iff_allSimplexComparisons p).2
    (allSimplexComparisons_of_epi_pullback H ((sharp_iff_allSimplexComparisons q).1 hq))

/-- The SAME original canonical base-change form of Rezk's epi sharp descent. -/
theorem sharp_of_baseChange_epi {X E Y : SSet.{u}}
    (p : X ⟶ Y) (e : E ⟶ Y) [Epi e]
    (hq : SharpComparisonDraft.Sharp (pullback.snd p e)) :
    SharpComparisonDraft.Sharp p :=
  sharp_of_epi_pullback (IsPullback.of_hasPullback p e) hq

end SSet.SharpSaturation
