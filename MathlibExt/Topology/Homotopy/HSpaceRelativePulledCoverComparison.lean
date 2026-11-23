/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceRelativeLowestRow
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexPulledCoverHomologyCocone
public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeCoefficientTransitions

/-!
# Ordinary integral homology gives the ACTUAL pulled-cover comparison

Every original relative homology coefficient vanishes by the derived
augmentation/lowest-row induction. Canonical evaluation identifies that
actual coefficient with the original simplex-fiber relative chain quotient.
The original homology exact sequence therefore makes the original fiber
map a homology isomorphism.

The SAME simplex lift gives both maps from those fibers to the literal
pulled native covers. Their complete original-map square is retained, and
both maps are derived weak from actual pullback squares. This derives
homology isomorphism of the actual pulled inclusion, for every original
point and degree. No cover homology, expected comparison or acyclicity
witness is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology
  HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section


namespace TopCat.HSpaceCommonUnitFibration

private theorem originalSimplexFiberMap_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))) (n : ℕ) :
    IsIso (SSet.homologyMap
      ((SSet.simplexPullbackDiagramMap (relativeInclusion f)
          (relativeInclusion_projection f)).app i)
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let α := Functor.whiskerRight
    (SSet.simplexPullbackDiagramMap (relativeInclusion f) (relativeInclusion_projection f))
    ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R)
  let : Mono (relativeInclusion f) := relativeInclusion_mono f
  let : Mono α := SSet.relativeSimplexChainArrow_mono (relativeInclusion f)
    (relativeInclusion_projection f) R
  let c := α.app i
  let : Mono c := inferInstance
  let : Mono (Arrow.mk c).hom := by
    change Mono c
    infer_instance
  let S := ShortComplex.cokernelSequence c
  let hS : S.ShortExact := ShortComplex.cokernelSequence_shortExact (Arrow.mk c)
  let e0 := eqToIso (congrArg
    (fun F : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))) ⥤
        ChainComplex AddCommGrpCat.{u} ℕ => F.obj i)
    (originalRelativeChainDiagram_eq f))
  let e := e0 ≪≫ HomologicalComplex.coefficientCokernelEvaluationIso α i
  have hRaw (k : ℕ) : IsZero ((cokernel c).homology k) :=
    IsZero.of_iso (originalRelativeHomologyCoefficients_isZero_of_integralHomology_isIso f h k i)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) k).mapIso e).symm
  have hG : HomologicalComplex.homologyMap S.g n = 0 :=
    IsZero.eq_zero_of_tgt (hRaw n) _
  let : Epi (HomologicalComplex.homologyMap c n) := (hS.homology_exact₂ n).epi_f hG
  let rel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl
  have hDelta : hS.δ (n + 1) n rel = 0 := IsZero.eq_zero_of_src (hRaw (n + 1)) _
  let : Mono (HomologicalComplex.homologyMap c n) :=
    (hS.homology_exact₁ (n + 1) n rel).mono_g hDelta
  have hc : IsIso (HomologicalComplex.homologyMap c n) := isIso_of_mono_of_epi _
  exact hc

/-- Ordinary Hiso of the arbitrary original map gives homology isomorphism of
its ACTUAL pulled inclusion, at EVERY original point and degree. -/
theorem originalPulledInclusion_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (x : X) (n : ℕ) :
    IsIso (SSet.homologyMap
      (SSet.KanComplex.nativeCoverBaseChangeMap (relativeInclusion f)
        (relativeInclusion_projection f)
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)))
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let G := SSet.FundamentalGroupoid (TopCat.toSSet.obj X)
  let B := CategoryTheory.nerve G
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm x)
  let p := unitProjection X
  let q := relativeProjection f
  let v := relativeInclusion f
  let H := SSet.homologyFunctor R n
  let σ : (Δ[0] : SSet.{u}) ⟶ B := SSet.const b
  let i : SSet.SimplexIndex B := CostructuredArrow.mk σ
  let L : {L : (Δ[0] : SSet.{u}) ⟶ SSet.KanComplex.nativeCover B b //
      L ≫ SSet.KanComplex.nativeCoverProjection B b = σ} :=
    ⟨SSet.const (SSet.KanComplex.nativeCoverIdentityPoint B b), by
      rw [SSet.const_comp, SSet.KanComplex.nativeCoverProjection_identityPoint]⟩
  let a := (SSet.simplexPullbackDiagramMap v (relativeInclusion_projection f)).app i
  let jp := SSet.KanComplex.simplexLiftToPulledCover p b σ L
  let jq := SSet.KanComplex.simplexLiftToPulledCover q b σ L
  let m := SSet.KanComplex.nativeCoverBaseChangeMap v (relativeInclusion_projection f) b
  let : (TopCat.toSSet.obj X).IsConnected := inferInstance
  let : CategoryTheory.IsConnected G :=
    SSet.fundamentalGroupoid_category_isConnected (TopCat.toSSet.obj X)
  let : Fibration p := unitProjection_isFibration X
  let : Fibration q := relativeProjection_fibration f
  have hp := SSet.simplexLiftToPulledCover_mem_realizationWeakEquivalences G p b σ L
  have hq := SSet.simplexLiftToPulledCover_mem_realizationWeakEquivalences G q b σ L
  let : QuasiIso (SSet.chainComplexMap jp R) := hp.quasiIso_chainComplexMap_addCommGrp R
  let : QuasiIso (SSet.chainComplexMap jq R) := hq.quasiIso_chainComplexMap_addCommGrp R
  let : IsIso (H.map jp) := (_root_.quasiIsoAt_iff_isIso_homologyMap _ n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap jp R) n)
  let : IsIso (H.map jq) := (_root_.quasiIsoAt_iff_isIso_homologyMap _ n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap jq R) n)
  let : IsIso (H.map a) := originalSimplexFiberMap_integralHomology_isIso f h i n
  have hSquare : H.map a ≫ H.map jq = H.map jp ≫ H.map m :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (SSet.KanComplex.simplexLiftToPulledCover_pairMap v
        (relativeInclusion_projection f) b σ L)).trans (H.map_comp _ _))
  have hComposite : IsIso (H.map (a ≫ jq)) :=
    (H.map_comp a jq).symm ▸
      (IsIso.comp_isIso' (inferInstance : IsIso (H.map a))
        (inferInstance : IsIso (H.map jq)))
  have hTarget : IsIso (H.map jp ≫ H.map m) :=
    ((H.map_comp a jq).trans hSquare) ▸ hComposite
  exact (isIso_comp_left_iff (H.map jp) (H.map m)).mp hTarget

end TopCat.HSpaceCommonUnitFibration
