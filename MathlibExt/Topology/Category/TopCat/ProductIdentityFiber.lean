/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.PathObjectProduct
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import MathlibExt.Topology.Category.TopCat.RealizedBasedWhitehead
import Mathlib.CategoryTheory.MorphismProperty.Limits
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead

/-!
# The actual ending-fiber projection for a product with an identity

The whole original path and point maps show that forgetting the identity
factor's path is a pullback of terminal path evaluation. Reversal transports
the existing initial-evaluation trivial fibration to terminal evaluation.
The original fiber projection is therefore a genuine trivial fibration,
without Kan, acyclicity, CW-model or expected weak-comparison input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

/-- Terminal evaluation is obtained from the existing trivial initial
evaluation by the actual interval-reversal Iso. -/
public theorem pathEvalOne_trivialFibration (Y : TopCat.{u}) :
    trivialFibrations TopCat.{u} (pathEvalOne Y) := by
  let p : pathObject Y ⟶ Y := pathEvalOne Y
  let q : pathObject Y ⟶ Y := pathEvalZero Y
  let : IsFibrant Y := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant Y
  let : Fibration (pathEndpoints Y) := modelCategory.pathEndpoints_fibration Y
  let : Fibration q := by
    change Fibration (pathEvalZero Y)
    have he : pathEvalZero Y = pathEndpoints Y ≫ (prod.fst : Y ⨯ Y ⟶ Y) := by
      simp [pathEndpoints]
    rw [he]
    infer_instance
  let : WeakEquivalence q :=
    (weakEquivalence_iff q).mpr (pathEvalZero_mem_weakHomotopyEquivalences Y)
  have hq : trivialFibrations TopCat.{u} q := mem_trivialFibrations q
  have h : (pathObjectReverseIso Y).hom ≫ q = p ≫ (Iso.refl Y).hom :=
    (pathObjectReverseIso_evalZero Y).trans (Category.comp_id p).symm
  let e : Arrow.mk p ≅ Arrow.mk q :=
    Arrow.isoMk (pathObjectReverseIso Y) (Iso.refl Y) h
  exact ((trivialFibrations TopCat.{u}).arrow_mk_iso_iff e).mpr
    hq

variable {X A : TopCat.{u}} (f : X ⟶ A) (Y : TopCat.{u}) (z : ↑(A ⨯ Y))

/-- The actual first ending-fiber projection, induced by the two original
product projections and their strict product-map square. -/
public def homotopyFiberProdIdentityProjection :
    homotopyFiber (prod.map f (𝟙 Y)) z ⟶
      homotopyFiber f ((prod.fst : A ⨯ Y ⟶ A) z) :=
  homotopyFiberMapOfSquare (prod.fst : X ⨯ Y ⟶ X) (prod.fst : A ⨯ Y ⟶ A)
    (prod.map_fst f (𝟙 Y)) z

public theorem productFiberProjection_toTotal :
    homotopyFiberProdIdentityProjection f Y z ≫
        homotopyFiberToTotal f ((prod.fst : A ⨯ Y ⟶ A) z) =
      homotopyFiberToTotal (prod.map f (𝟙 Y)) z ≫ (prod.fst : X ⨯ Y ⟶ X) := by
  unfold homotopyFiberProdIdentityProjection
  exact homotopyFiberMapOfSquare_toTotal (prod.fst : X ⨯ Y ⟶ X)
      (prod.fst : A ⨯ Y ⟶ A) (prod.map_fst f (𝟙 Y)) z

private theorem productFiberProjection_path :
    homotopyFiberProdIdentityProjection f Y z ≫
        homotopyFiberPath f ((prod.fst : A ⨯ Y ⟶ A) z) =
      homotopyFiberPath (prod.map f (𝟙 Y)) z ≫ pathObjectMap (prod.fst : A ⨯ Y ⟶ A) := by
  unfold homotopyFiberProdIdentityProjection
  exact homotopyFiberMapOfSquare_path (prod.fst : X ⨯ Y ⟶ X)
      (prod.fst : A ⨯ Y ⟶ A) (prod.map_fst f (𝟙 Y)) z

private def productFiberYPath :
    homotopyFiber (prod.map f (𝟙 Y)) z ⟶ pathObject Y :=
  homotopyFiberPath (prod.map f (𝟙 Y)) z ≫ pathObjectMap (prod.snd : A ⨯ Y ⟶ Y)

private theorem productFiberYPath_zero :
    productFiberYPath f Y z ≫ pathEvalZero Y =
      homotopyFiberToTotal (prod.map f (𝟙 Y)) z ≫ (prod.snd : X ⨯ Y ⟶ Y) := by
  change (homotopyFiberPath (prod.map f (𝟙 Y)) z ≫ pathObjectMap prod.snd) ≫ _ = _
  calc
    _ = homotopyFiberPath (prod.map f (𝟙 Y)) z ≫
        (pathEvalZero (A ⨯ Y) ≫ (prod.snd : A ⨯ Y ⟶ Y)) := by
      rw [Category.assoc, pathObjectMap_evalZero]
    _ = (homotopyFiberToTotal (prod.map f (𝟙 Y)) z ≫ prod.map f (𝟙 Y)) ≫
        (prod.snd : A ⨯ Y ⟶ Y) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun m => m ≫ (prod.snd : A ⨯ Y ⟶ Y))
          (homotopyPullbackPath_evalZero (prod.map f (𝟙 Y)) (TopCat.const z)))
    _ = _ := by simp only [Category.assoc, prod.map_snd, Category.comp_id]

private theorem productFiberYPath_one :
    productFiberYPath f Y z ≫ pathEvalOne Y =
      TopCat.const ((prod.snd : A ⨯ Y ⟶ Y) z) := by
  ext w
  have h := ConcreteCategory.congr_hom
    (homotopyPullbackPath_evalOne (prod.map f (𝟙 Y)) (TopCat.const z)) w
  change (prod.snd : A ⨯ Y ⟶ Y) ((homotopyFiberPath (prod.map f (𝟙 Y)) z w) 1) =
    (prod.snd : A ⨯ Y ⟶ Y) z
  exact congrArg (prod.snd : A ⨯ Y ⟶ Y) h

private def endpointPullbackLift {W E V B : TopCat.{u}} {p : E ⟶ B} {h : V ⟶ B}
    (l : W ⟶ E) (r : W ⟶ V) (γ : W ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    W ⟶ homotopyPullback p h :=
  pullback.lift (prod.lift l r) γ (by
    apply prod.hom_ext
    · simpa only [pathEndpoints, Category.assoc, prod.lift_fst, prod.map_fst,
        prod.lift_fst_assoc] using h₀.symm
    · simpa only [pathEndpoints, Category.assoc, prod.lift_snd, prod.map_snd,
        prod.lift_snd_assoc] using h₁.symm)

private theorem endpointPullbackLift_left {W E V B : TopCat.{u}} {p : E ⟶ B} {h : V ⟶ B}
    (l : W ⟶ E) (r : W ⟶ V) (γ : W ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    endpointPullbackLift l r γ h₀ h₁ ≫ homotopyPullbackLeft p h = l := by
  rw [endpointPullbackLift, homotopyPullbackLeft, ← Category.assoc, pullback.lift_fst]
  exact prod.lift_fst l r

private theorem endpointPullbackLift_path {W E V B : TopCat.{u}} {p : E ⟶ B} {h : V ⟶ B}
    (l : W ⟶ E) (r : W ⟶ V) (γ : W ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    endpointPullbackLift l r γ h₀ h₁ ≫ homotopyPullbackPath p h = γ := by
  rw [endpointPullbackLift, pullback.lift_snd]

/-- The SAME original ending-fiber projection is the pullback of the actual
terminal path evaluation. Its top leg keeps the entire second-factor path. -/
public theorem homotopyFiber_prodIdentity_isPullback :
    IsPullback
      (homotopyFiberPath (prod.map f (𝟙 Y)) z ≫ pathObjectMap (prod.snd : A ⨯ Y ⟶ Y))
      (homotopyFiberProdIdentityProjection f Y z)
      (pathEvalOne Y)
      (TopCat.const ((prod.snd : A ⨯ Y ⟶ Y) z)) := by
  let FP := homotopyFiber (prod.map f (𝟙 Y)) z
  let FI := homotopyFiber f ((prod.fst : A ⨯ Y ⟶ A) z)
  let q : FP ⟶ FI := homotopyFiberProdIdentityProjection f Y z
  let r : FP ⟶ pathObject Y := productFiberYPath f Y z
  let c : FI ⟶ Y := TopCat.const ((prod.snd : A ⨯ Y ⟶ Y) z)
  have hc : r ≫ pathEvalOne Y = q ≫ c :=
    (productFiberYPath_one f Y z).trans (by ext w; rfl)
  let cone := PullbackCone.mk r q hc
  apply IsPullback.of_isLimit (c := cone)
  refine PullbackCone.isLimitAux' cone ?_
  intro S
  let total : S.pt ⟶ X ⨯ Y := prod.lift
    (S.snd ≫ homotopyFiberToTotal f ((prod.fst : A ⨯ Y ⟶ A) z))
    (S.fst ≫ pathEvalZero Y)
  let ρ : S.pt ⟶ pathObject (A ⨯ Y) :=
    prod.lift (S.snd ≫ homotopyFiberPath f ((prod.fst : A ⨯ Y ⟶ A) z)) S.fst ≫
      (pathObjectProductIso A Y).inv
  have h₀ : ρ ≫ pathEvalZero (A ⨯ Y) = total ≫ prod.map f (𝟙 Y) := by
    apply prod.hom_ext
    · simp only [ρ, total, Category.assoc, pathObjectProductIso_inv_evalZero_fst,
        prod.lift_fst_assoc, prod.map_fst]
      exact congrArg (fun m => S.snd ≫ m)
        (homotopyPullbackPath_evalZero f
          (TopCat.const ((prod.fst : A ⨯ Y ⟶ A) z)))
    · simp only [ρ, total, Category.assoc, pathObjectProductIso_inv_evalZero_snd,
        prod.lift_snd_assoc, prod.map_snd, Category.comp_id]
      exact (prod.lift_snd _ _).symm
  have h₁ : ρ ≫ pathEvalOne (A ⨯ Y) = TopCat.const (X := S.pt) z := by
    apply prod.hom_ext
    · simp only [ρ, Category.assoc, pathObjectProductIso_inv_evalOne_fst,
        prod.lift_fst_assoc]
      refine (congrArg (fun m => S.snd ≫ m)
        (homotopyPullbackPath_evalOne f
          (TopCat.const ((prod.fst : A ⨯ Y ⟶ A) z)))).trans ?_
      ext w
      rfl
    · simp only [ρ, Category.assoc, pathObjectProductIso_inv_evalOne_snd,
        prod.lift_snd_assoc]
      refine S.condition.trans ?_
      ext w
      rfl
  let point : S.pt ⟶ TopCat.of PUnit := TopCat.const PUnit.unit
  have h₁' : ρ ≫ pathEvalOne (A ⨯ Y) = point ≫ TopCat.const z :=
    h₁.trans (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro w
      have hL : (TopCat.const (X := S.pt) z).hom w = z :=
        TopCat.const_apply (X := S.pt) z w
      have hComp : (point ≫ TopCat.const z).hom w =
          (TopCat.const (X := TopCat.of PUnit.{u + 1}) z).hom (point.hom w) :=
        congrArg (fun k : C(S.pt, ↑(A ⨯ Y)) => k w)
          (TopCat.hom_comp point (TopCat.const (X := TopCat.of PUnit.{u + 1}) z))
      have hR : (TopCat.const (X := TopCat.of PUnit.{u + 1}) z).hom (point.hom w) = z :=
        TopCat.const_apply (X := TopCat.of PUnit.{u + 1}) z (point.hom w)
      exact hL.trans (hComp.trans hR).symm)
  let l : S.pt ⟶ FP := endpointPullbackLift total point ρ h₀ h₁'
  have hlTotal : l ≫ homotopyFiberToTotal (prod.map f (𝟙 Y)) z = total :=
    endpointPullbackLift_left total point ρ h₀ h₁'
  have hlPath : l ≫ homotopyFiberPath (prod.map f (𝟙 Y)) z = ρ :=
    endpointPullbackLift_path total point ρ h₀ h₁'
  have hlr : l ≫ r = S.fst := by
    change l ≫ (homotopyFiberPath (prod.map f (𝟙 Y)) z ≫ pathObjectMap prod.snd) = _
    rw [← Category.assoc, hlPath]
    simp only [ρ, Category.assoc, pathObjectProductIso_inv_snd, prod.lift_snd]
  have hlq : l ≫ q = S.snd := by
    apply homotopyPullback_hom_ext
    · change (l ≫ q) ≫ homotopyFiberToTotal f _ = _
      rw [Category.assoc, productFiberProjection_toTotal, ← Category.assoc, hlTotal]
      exact prod.lift_fst _ _
    · exact isTerminalPUnit.hom_ext _ _
    · change (l ≫ q) ≫ homotopyFiberPath f _ = _
      rw [Category.assoc, productFiberProjection_path, ← Category.assoc, hlPath]
      simp only [ρ, Category.assoc, pathObjectProductIso_inv_fst, prod.lift_fst]
  refine ⟨l, hlr, hlq, ?_⟩
  intro m hmr hmq
  have hr : m ≫ r = l ≫ r := hmr.trans hlr.symm
  have hq : m ≫ q = l ≫ q := hmq.trans hlq.symm
  apply homotopyPullback_hom_ext
  · apply prod.hom_ext
    · simpa only [q, Category.assoc, productFiberProjection_toTotal] using
        congrArg (fun k => k ≫ homotopyFiberToTotal f ((prod.fst : A ⨯ Y ⟶ A) z)) hq
    · simpa only [r, Category.assoc, productFiberYPath_zero] using
        congrArg (fun k => k ≫ pathEvalZero Y) hr
  · exact isTerminalPUnit.hom_ext _ _
  · apply (cancel_mono (pathObjectProductIso A Y).hom).mp
    apply prod.hom_ext
    · simpa only [q, Category.assoc, pathObjectProductIso_hom_fst,
        productFiberProjection_path] using
        congrArg (fun k => k ≫ homotopyFiberPath f ((prod.fst : A ⨯ Y ⟶ A) z)) hq
    · simpa only [r, productFiberYPath, Category.assoc,
        pathObjectProductIso_hom_snd] using hr

/-- The original product ending-fiber projection is genuinely trivial;
it is not an outer weak-comparison input. -/
public theorem homotopyFiberProdIdentityProjection_trivialFibration :
    trivialFibrations TopCat.{u} (homotopyFiberProdIdentityProjection f Y z) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := trivialFibrations TopCat.{u}) (homotopyFiber_prodIdentity_isPullback f Y z)
    (pathEvalOne_trivialFibration Y)

/-- Its weak membership follows from the derived trivial fibration. -/
public theorem homotopyFiberProdIdentityProjection_mem_weakHomotopyEquivalences :
    weakHomotopyEquivalences (homotopyFiberProdIdentityProjection f Y z) := by
  have h := (mem_trivialFibrations_iff _).mp
    (homotopyFiberProdIdentityProjection_trivialFibration f Y z)
  exact (weakEquivalence_iff _).mp h.2

end TopCat

end
