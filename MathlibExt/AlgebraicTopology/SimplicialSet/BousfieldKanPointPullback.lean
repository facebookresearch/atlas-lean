/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointFiberComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatStrictFiberHomotopyFiber

import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono

/-!
# Strict point fibers of a Bousfield--Kan homotopy colimit

The canonical constant-chain inclusion `bkPointInclusion E j` is the strict
simplicial fiber of `bkHocolimToNerve E` over the vertex at `j`. Since a vertex
is a simplicial monomorphism, realization preserves this pullback square. The
resulting strict-fiber isomorphism factors the actual `bkPointFiberComparison`
through `TopCat.strictFiberToHomotopyFiber`.

These identifications hold for every diagram. No equivalence claim about the
homotopy-fiber comparison follows here from transition maps. That separate
claim requires the homotopy-fiber descent in Quillen, *Higher algebraic K-theory I*,
LNM 341 (1973), p. 98, or Weibel, *The K-book*, IV.3.6.1(ii).

The adjustment from the realization of `Δ[0]` to `PUnit` follows the existing
strict-fiber comparison in `SSet.ModelCategory.HomotopyFiberRealization`.
-/

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

universe u v w

variable {J : Type u} [Category.{v} J]

private noncomputable def bkDegreeIso (E : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkHocolim E).obj (op ⦋n⦌) ≅
      (Σ p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n,
        (E.obj p.1.left).obj (op ⦋n⦌)) :=
  sigmaObjIso (fun p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => E.obj p.1.left) (op ⦋n⦌) ≪≫
    Types.coproductIso (fun p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => (E.obj p.1.left).obj (op ⦋n⦌))

private theorem bkDegreeIso_hom_inclusion (E : J ⥤ SSet.{max u v}) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) ≫
        (bkDegreeIso E n).hom = ↾fun x => ⟨p, x⟩ := by
  change (Sigma.ι (fun p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => E.obj p.1.left) p).app (op ⦋n⦌) ≫
    ((sigmaObjIso _ (op ⦋n⦌)).hom ≫ (Types.coproductIso _).hom) = _
  rw [← Category.assoc, ι_comp_sigmaObjIso_hom, Types.coproductIso_ι_comp_hom]

private theorem bkHocolimToNerve_wbarIncl (E : J ⥤ SSet.{max u v}) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) ≫
        (bkHocolimToNerve E).app (op ⦋n⦌) = ↾fun _ => p.1 := by
  change _ ≫ ((bkHocolimMap (bkDiagramToPoint E)).app (op ⦋n⦌) ≫
    (bkPointIsoNerve J).hom.app (op ⦋n⦌)) = _
  rw [← Category.assoc, bkHocolimMap_app_mk_ι, Category.assoc,
    bkPointIsoNerve_hom_wbarIncl]
  rfl

private theorem bkDegreeIso_inv_inclusion (E : J ⥤ SSet.{max u v}) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (↾fun x => ⟨p, x⟩) ≫ (bkDegreeIso E n).inv =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) := by
  rw [← bkDegreeIso_hom_inclusion E n p, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem bkDegreeIso_inv_projection (E : J ⥤ SSet.{max u v}) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (E.obj p.1.left).obj (op ⦋n⦌)) :
    (bkHocolimToNerve E).app (op ⦋n⦌) ((bkDegreeIso E n).inv ⟨p, x⟩) = p.1 := by
  have hι := ConcreteCategory.congr_hom (bkDegreeIso_inv_inclusion E n p) x
  change (bkDegreeIso E n).inv ⟨p, x⟩ =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) x at hι
  rw [hι]
  have hπ := ConcreteCategory.congr_hom (bkHocolimToNerve_wbarIncl E n p) x
  change (bkHocolimToNerve E).app (op ⦋n⦌)
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) x) = p.1 at hπ
  exact hπ

/-- The canonical constant-chain inclusion is a simplicial monomorphism. -/
instance instMonoBkPointInclusion (E : J ⥤ SSet.{max u v}) (j : J) :
    Mono (bkPointInclusion E j) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro x y h
  have h' := congrArg ((bkDegreeIso E n).hom) h
  rw [bkPointInclusion_app_mk] at h'
  change (bkDegreeIso E n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)).app (op ⦋n⦌) x) =
    (bkDegreeIso E n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)).app (op ⦋n⦌) y) at h'
  have hι := bkDegreeIso_hom_inclusion E n (bkPointWeightedIndex j n)
  have hx := ConcreteCategory.congr_hom hι x
  have hy := ConcreteCategory.congr_hom hι y
  change (bkDegreeIso E n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)).app (op ⦋n⦌) x) =
    ⟨bkPointWeightedIndex j n, x⟩ at hx
  change (bkDegreeIso E n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)).app (op ⦋n⦌) y) =
    ⟨bkPointWeightedIndex j n, y⟩ at hy
  rw [hx, hy] at h'
  exact eq_of_heq (Sigma.mk.inj_iff.mp h').2

/-- A diagram value is the strict simplicial fiber of the BK projection over the
vertex selected by its indexing object, with the canonical constant-chain inclusion. -/
theorem bkPointInclusion_isPullback (E : J ⥤ SSet.{max u v}) (j : J) :
    IsPullback (bkPointInclusion E j) (stdSimplex.isTerminalObj₀.from (E.obj j))
      (bkHocolimToNerve E)
      (SSet.const (X := Δ[0]) (ComposableArrows.mk₀ j)) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨n⟩⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hw : bkPointInclusion E j ≫ bkHocolimToNerve E =
        stdSimplex.isTerminalObj₀.from (E.obj j) ≫
          SSet.const (X := Δ[0]) (ComposableArrows.mk₀ j) := by
      rw [SSet.comp_const]
      exact bkPointInclusion_comp_bkHocolimToNerve E j
    exact congrArg (fun f : E.obj j ⟶ nerve J => f.app (op ⦋n⦌)) hw
  · intro x y h
    have hm := instMonoBkPointInclusion E j
    rw [NatTrans.mono_iff_mono_app] at hm
    exact (mono_iff_injective _).mp (hm (op ⦋n⦌)) h.1
  · intro z v h
    obtain ⟨⟨p, x⟩, rfl⟩ := (bkDegreeIso E n).toEquiv.symm.surjective z
    have hp : p.1 = SrepBridge.constChain j n := by
      change (bkHocolimToNerve E).app (op ⦋n⦌)
        ((bkDegreeIso E n).inv ⟨p, x⟩) = SrepBridge.constChain j n at h
      exact (bkDegreeIso_inv_projection E n p x).symm.trans h
    have hp' : p = bkPointWeightedIndex j n := by
      rcases p with ⟨s, w⟩
      change PUnit at w
      cases w
      cases hp
      rfl
    subst p
    refine ⟨x, ?_, ?_⟩
    · rw [bkPointInclusion_app_mk]
      exact (ConcreteCategory.congr_hom
        (bkDegreeIso_inv_inclusion E n (bkPointWeightedIndex j n)) x).symm
    · apply stdSimplex.objEquiv.injective
      subsingleton

private theorem bkVertex_mono (j : J) :
    Mono (SSet.const (X := Δ[0]) (Y := nerve J) (ComposableArrows.mk₀ j)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y _
  apply stdSimplex.objEquiv.injective
  subsingleton

/-- Realization preserves the strict point-fiber square for the BK projection. -/
theorem bkPointInclusion_realized_isPullback
    (E : J ⥤ SSet.{max u v}) (j : J) :
    IsPullback (toTop.map (bkPointInclusion E j))
      (toTop.map (stdSimplex.isTerminalObj₀.from (E.obj j)))
      (toTop.map (bkHocolimToNerve E))
      (toTop.map (SSet.const (X := Δ[0]) (ComposableArrows.mk₀ j))) := by
  let _ := bkVertex_mono j
  exact ((bkPointInclusion_isPullback E j).flip.map_toTop_of_mono).flip

private noncomputable def bkRealizedZeroIsTerminal :
    IsTerminal (toTop.obj (Δ[0] : SSet.{w})) := by
  let _ : ∀ Y : TopCat.{w}, Unique (Y ⟶ toTop.obj (Δ[0] : SSet.{w})) := fun Y =>
    { default := TopCat.ofHom ⟨fun _ => default, continuous_const⟩
      uniq := by
        intro f
        apply TopCat.hom_ext
        ext y
        exact Subsingleton.elim _ _ }
  exact IsTerminal.ofUnique _

private noncomputable def bkRealizedZeroIso :
    toTop.obj (Δ[0] : SSet.{w}) ≅ TopCat.of PUnit :=
  bkRealizedZeroIsTerminal.uniqueUpToIso TopCat.isTerminalPUnit

private theorem bkPointInclusion_realized_strictPullback
    (E : J ⥤ SSet.{max u v}) (j : J) :
    IsPullback (toTop.map (bkPointInclusion E j))
      (TopCat.isTerminalPUnit.from _)
      (toTop.map (bkHocolimToNerve E))
      (TopCat.const (X := TopCat.of PUnit) (bkPointRealizedVertex j)) := by
  have h := bkPointInclusion_realized_isPullback E j
  apply h.of_iso (Iso.refl _) (Iso.refl _) bkRealizedZeroIso (Iso.refl _)
  · simp
  · apply TopCat.isTerminalPUnit.hom_ext
  · simp
  · apply TopCat.ext
    intro x
    exact DFunLike.congr_fun (toTop_map_const_hom (A := Δ[0]) (Y := nerve J)
      (ComposableArrows.mk₀ j)) x

/-- The realization of a diagram value is canonically isomorphic to the strict
point fiber of the realized BK projection. -/
noncomputable def bkPointStrictFiberIso (E : J ⥤ SSet.{max u v}) (j : J) :
    toTop.obj (E.obj j) ≅
      pullback (toTop.map (bkHocolimToNerve E))
        (TopCat.const (X := TopCat.of PUnit) (bkPointRealizedVertex j)) := by
  exact (bkPointInclusion_realized_strictPullback E j).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- The strict-fiber identification retains the actual constant-chain inclusion. -/
@[reassoc (attr := simp)]
theorem bkPointStrictFiberIso_hom_fst (E : J ⥤ SSet.{max u v}) (j : J) :
    (bkPointStrictFiberIso E j).hom ≫
      pullback.fst (toTop.map (bkHocolimToNerve E))
        (TopCat.const (X := TopCat.of PUnit) (bkPointRealizedVertex j)) =
      toTop.map (bkPointInclusion E j) :=
  (bkPointInclusion_realized_strictPullback E j).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback _ _)

/-- The canonical BK point-fiber comparison is the strict-fiber identification
followed by the constant-path comparison into the homotopy fiber. -/
theorem bkPointStrictFiberIso_hom_comp_strictFiberToHomotopyFiber
    (E : J ⥤ SSet.{max u v}) (j : J) :
    (bkPointStrictFiberIso E j).hom ≫
      TopCat.strictFiberToHomotopyFiber (toTop.map (bkHocolimToNerve E))
        (bkPointRealizedVertex j) = bkPointFiberComparison E j := by
  apply TopCat.homotopyPullback_hom_ext
  · rw [Category.assoc, TopCat.strictFiberToHomotopyFiber_toTotal,
      bkPointStrictFiberIso_hom_fst, bkPointFiberComparison_toTotal]
  · apply TopCat.isTerminalPUnit.hom_ext
  · rw [Category.assoc, TopCat.strictFiberToHomotopyFiber_path,
      bkPointFiberComparison_path]
    apply TopCat.ext
    intro z
    rfl

end SSet

end
