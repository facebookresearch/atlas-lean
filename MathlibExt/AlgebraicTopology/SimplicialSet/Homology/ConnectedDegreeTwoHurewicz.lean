/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.DegreeTwoHurewiczInverse
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceHomotopyGroupIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOver
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains

public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.PointedTwoNormalization
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BasedPathLoop
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHomologyComparisonNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic.Abel

/-!
# The degree-two Hurewicz map of a one-connected Kan complex

The actual minimal-core retraction induces the homotopy and homology
comparisons at the original basepoint, with core point `r(x)`. The already
proved Kan weak-equivalence chain theorem supplies the actual normalized
chain-map quasi-isomorphism of this constructed retraction. The core
Hurewicz equivalence is the actual production one-reduced theorem. Naturality
identifies the resulting bijection with the existing native Hurewicz map.

No desired Hurewicz equivalence, homology isomorphism, weak equivalence, or
basepoint-membership witness is supplied as a premise.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped Simplicial
open SSet.modelCategoryQuillen

universe u

namespace SSet

namespace MinimalFibration.MinimalSubfibration

variable {X : SSet.{u}} [KanComplex X]

/-- Reverse the actual relative deformation over the terminal object using
its Kan fibration. The original endpoint maps and stationarity are retained. -/
private noncomputable def reverseDeformationOverTerminal
    (M : MinimalSubfibration (terminal.from X)) :
    SSet.Homotopy (M.sdr.r ≫ M.carrier.ι) (𝟙 X) := by
  let _ : Fibration (terminal.from X) := by
    change KanComplex X
    infer_instance
  let H : HomotopyRelOver (terminal.from X) (𝟙 X)
      (M.sdr.r ≫ M.carrier.ι) (Subcomplex.range M.carrier.ι) :=
    { toHomotopyRel := M.sdr.homotopy
      over := terminal.hom_ext _ _ }
  exact H.symm.toHomotopyRel.toHomotopy

/-- The other composite is literally the core identity. -/
private noncomputable def coreCompositeHomotopy
    (M : MinimalSubfibration (terminal.from X)) :
    SSet.Homotopy (M.carrier.ι ≫ M.sdr.r) (𝟙 (M.carrier : SSet.{u})) := by
  rw [M.sdr.retract]
  exact (HomotopyRel.refl (𝟙 (M.carrier : SSet.{u})) ⊥).toHomotopy

/-- The actual retraction is a native Kan weak equivalence, from its
constructed homotopy inverse pair. No weak-equivalence premise is assumed. -/
private theorem retractionW (M : MinimalSubfibration (terminal.from X)) :
    KanComplex.W M.sdr.r :=
  KanComplex.W.of_homotopy M.sdr.r M.carrier.ι
    M.reverseDeformationOverTerminal M.coreCompositeHomotopy

/-- Trivial π₁ is transported to `r(x)`, without assuming that `x` lies in the core. -/
private theorem piOne_subsingleton_at_retract
    (M : MinimalSubfibration (terminal.from X)) (x : X _⦋0⦌)
    [Subsingleton (KanComplex.π 1 X x)] :
    Subsingleton (KanComplex.π 1 (M.carrier : SSet.{u}) (M.sdr.r.app _ x)) := by
  let e := KanComplex.W.homotopyGroupEquiv M.sdr.r M.retractionW 1 x
  constructor
  intro a b
  apply e.symm.injective
  exact Subsingleton.elim _ _

/-- The derived one-reduced condition at the exact retracted basepoint. -/
private theorem edges_degenerate_at_retract
    (M : MinimalSubfibration (terminal.from X)) [X.IsConnected] (x : X _⦋0⦌)
    [Subsingleton (KanComplex.π 1 X x)] :
    ∀ s : (M.carrier : SSet.{u}) _⦋1⦌,
      s = (M.carrier : SSet.{u}).σ 0 (M.sdr.r.app _ x) := by
  let _ : (M.carrier : SSet.{u}).IsConnected := M.carrier_isConnected
  let _ : Subsingleton (KanComplex.π 1 (M.carrier : SSet.{u}) (M.sdr.r.app _ x)) :=
    M.piOne_subsingleton_at_retract x
  exact edge_eq_sigmaZero_of_isConnected_of_isMinimal_of_piOne_subsingleton
    M.carrier M.carrier_isMinimal (M.sdr.r.app _ x)

/-- The actual integral homology map of the retraction is an isomorphism,
using the existing normalized-chain invariance theorem for the constructed
Kan weak equivalence. -/
private noncomputable def retractionIntegralHomologyIso
    (M : MinimalSubfibration (terminal.from X)) (n : ℕ) :
    (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology n ≅
      ((M.carrier : SSet.{u}).normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology n :=
  let f := normalizedChainComplexMap M.sdr.r
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let _ : QuasiIso f :=
    KanComplex.W.quasiIso_normalizedChainComplexMap M.retractionW
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  isoOfQuasiIsoAt f n

@[simp]
private theorem retractionIntegralHomologyIso_hom
    (M : MinimalSubfibration (terminal.from X)) (n : ℕ) :
    (M.retractionIntegralHomologyIso n).hom =
      HomologicalComplex.homologyMap
        (normalizedChainComplexMap M.sdr.r
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) n :=
  rfl

end MinimalFibration.MinimalSubfibration

/-- The exact underlying-element naturality square for the original native
Hurewicz map, obtained by evaluation of its proved morphism-valued formula. -/
theorem degreeTwoHurewiczElement_naturality
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (f : X ⟶ Y) (hxy : f.app _ x = y)
    (a : KanComplex.π 2 X x) :
    Multiplicative.toAdd (degreeTwoHurewiczElementMulHom y (KanComplex.π.map f hxy 2 a)) =
      HomologicalComplex.homologyMap
        (normalizedChainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2
        (Multiplicative.toAdd (degreeTwoHurewiczElementMulHom x a)) := by
  have h := ConcreteCategory.congr_hom
    (degreeTwoHurewiczFn_naturality f hxy a) (ULift.up (1 : ℤ))
  exact h

/-- Bijectivity of the original Hurewicz map for an actual one-connected Kan
complex. All comparison maps are constructed from the actual minimal core. -/
theorem degreeTwoHurewiczElementMulHom_bijective_of_oneConnected
    {X : SSet.{u}} [KanComplex X] [X.IsConnected] (x : X _⦋0⦌)
    [Subsingleton (KanComplex.π 1 X x)] :
    Function.Bijective (degreeTwoHurewiczElementMulHom x) := by
  let M := MinimalFibration.chosenMinimalCore X
  let m : (M.carrier : SSet.{u}) _⦋0⦌ := M.sdr.r.app _ x
  let HX := (X.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2
  let HM := ((M.carrier : SSet.{u}).normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2
  let pr : KanComplex.π 2 X x → KanComplex.π 2 (M.carrier : SSet.{u}) m :=
    KanComplex.π.map M.sdr.r rfl 2
  let hr : HX → HM := HomologicalComplex.homologyMap
    (normalizedChainComplexMap M.sdr.r
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2
  let FX : KanComplex.π 2 X x → HX := fun a =>
    Multiplicative.toAdd (degreeTwoHurewiczElementMulHom x a)
  let FM : KanComplex.π 2 (M.carrier : SSet.{u}) m → HM := fun a =>
    Multiplicative.toAdd (degreeTwoHurewiczElementMulHom m a)
  have hpr : Function.Bijective pr :=
    KanComplex.W.bijective_piMap M.retractionW 2 x
  have hhr : Function.Bijective hr :=
    (M.retractionIntegralHomologyIso 2).addCommGroupIsoToAddEquiv.bijective
  have hedgeM := M.edges_degenerate_at_retract x
  have hFM : Function.Bijective FM :=
    (Multiplicative.toAdd : Multiplicative HM ≃ HM).bijective.comp
      (degreeTwoHurewiczElementMulHom_bijective m hedgeM)
  have hsquare : hr ∘ FX = FM ∘ pr := by
    funext a
    exact (degreeTwoHurewiczElement_naturality M.sdr.r rfl a).symm
  have hcomp : Function.Bijective (hr ∘ FX) :=
    hsquare.symm ▸ (hFM.comp hpr)
  have hFX : Function.Bijective FX :=
    (Function.Bijective.of_comp_iff' hhr FX).mp hcomp
  exact (Multiplicative.ofAdd : HX ≃ Multiplicative HX).bijective.comp hFX

/-- The canonical equivalence uses the original native Hurewicz function,
independently of the nonfunctorial choice of minimal core used in the proof. -/
noncomputable def connectedDegreeTwoHurewiczEquiv
    {X : SSet.{u}} [KanComplex X] [X.IsConnected] (x : X _⦋0⦌)
    [Subsingleton (KanComplex.π 1 X x)] :
    KanComplex.π 2 X x ≃* Multiplicative
      ((X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2) :=
  MulEquiv.ofBijective (degreeTwoHurewiczElementMulHom x)
    (degreeTwoHurewiczElementMulHom_bijective_of_oneConnected x)

@[simp]
theorem connectedDegreeTwoHurewiczEquiv_apply
    {X : SSet.{u}} [KanComplex X] [X.IsConnected] (x : X _⦋0⦌)
    [Subsingleton (KanComplex.π 1 X x)] (a : KanComplex.π 2 X x) :
    connectedDegreeTwoHurewiczEquiv x a = degreeTwoHurewiczElementMulHom x a :=
  rfl

@[simp]
theorem connectedDegreeTwoHurewiczEquiv_mk
    {X : SSet.{u}} [KanComplex X] [X.IsConnected] (x : X _⦋0⦌)
    [Subsingleton (KanComplex.π 1 X x)] (p : X.PtSimplex 2 x) :
    connectedDegreeTwoHurewiczEquiv x (KanComplex.π.mk p) =
      Multiplicative.ofAdd (pointedTwoHomologyClass p (ULift.up (1 : ℤ))) :=
  degreeTwoHurewiczElementMulHom_mk x p

theorem connectedDegreeTwoHurewiczEquiv_naturality
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] [X.IsConnected] [Y.IsConnected]
    {x : X _⦋0⦌} {y : Y _⦋0⦌}
    [Subsingleton (KanComplex.π 1 X x)] [Subsingleton (KanComplex.π 1 Y y)]
    (f : X ⟶ Y) (hxy : f.app _ x = y) (a : KanComplex.π 2 X x) :
    Multiplicative.toAdd (connectedDegreeTwoHurewiczEquiv y (KanComplex.π.map f hxy 2 a)) =
      HomologicalComplex.homologyMap
        (normalizedChainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2
        (Multiplicative.toAdd (connectedDegreeTwoHurewiczEquiv x a)) :=
  degreeTwoHurewiczElement_naturality f hxy a

end SSet


/-!
## The original native loop and degree-two homology comparison

The source-first based-path evaluation gives the signed chain comparison
and its positive cycle formula. The original native fundamental-group
comparison contributes the inverse edge. Their two proved signs give the
original all-Kan degree-two Hurewicz/loop-connecting square through the
actual normalization inclusion. Fixed sphere calibration remains separate.
-/

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial
open scoped Simplicial

namespace SSet

/-- The actual original based-path evaluation homotopy, with source first
and the original simplicial interval second. -/
def basedPathEvaluationHomotopy (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.Homotopy (SSet.const x : basedPath X x ⟶ X) (basedPathProj X x) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm (SSet.const x : basedPath X x ⟶ X))
    (SSet.RelativeMorphism.botEquiv.symm (basedPathProj X x))
  refine
    { h := (β_ (basedPath X x) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry
          (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι
      h₀ := ?_
      h₁ := ?_
      rel := by ext n ⟨⟨a, ha⟩, t⟩; cases ha }
  · change SSet.ι₀ ≫ (β_ (basedPath X x) (Δ[1] : SSet.{u})).hom ≫
      MonoidalClosed.uncurry (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι =
      SSet.const x
    dsimp only [basedPath]
    rw [← comp_eval₀_eq_ι₀_braiding_uncurry]
    exact Subcomplex.fiber_ι_comp (eval₀ : pathSpace X ⟶ X) x
  · change SSet.ι₁ ≫ (β_ (basedPath X x) (Δ[1] : SSet.{u})).hom ≫
      MonoidalClosed.uncurry (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι =
      (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ≫ eval₁
    exact (comp_eval₁_eq_ι₁_braiding_uncurry
      (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι).symm

theorem basedPathEvaluationHomotopy_h (X : SSet.{u}) (x : X _⦋0⦌) :
    (basedPathEvaluationHomotopy X x).h =
      (β_ (basedPath X x) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry
          (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι := rfl

/-!
Original based-path evaluation / chosen last-face connecting
representative chain identities, with actual integral coefficients.
The actual evaluation homotopy is constructed, not a witness parameter.
-/

private def evaluationChosenLiftChain
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      ((basedPath X x).chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).X 2 :=
  (basedPath X x).ιChainComplex
    (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
    (ConnectingMap.chosenLift (e := basedPathPoint X x)
      (basedPathProj X x) (basedPathProj_basedPathPoint X x) σ)

/-- Apply the actual source-first evaluation chain operator to the original
chosen last face of the based-path connecting lift. -/
def evaluationConnectingChain
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).X 2 :=
  (basedPath X x).ιChainComplex
      (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
      (yonedaEquiv (RelativeMorphism.map
        (ConnectingMap.chosenLiftPt (e := basedPathPoint X x)
          (basedPathProj X x) (basedPathProj_basedPathPoint X x) σ))) ≫
    ((basedPathEvaluationHomotopy X x).chainComplexMap
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).hom 1 2

/-- The evaluation chain uses the actual connecting representative in the
original strict loop fiber and its original inclusion into based paths. -/
theorem evaluationConnectingChain_eq_fiber_representative
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    evaluationConnectingChain X x σ =
      ((loopSpace X x).ιChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
          (yonedaEquiv (RelativeMorphism.map
            (ConnectingMap.connectingPtSimplexRep
              (p := basedPathProj X x) (e := basedPathPoint X x)
              (basedPathProj_basedPathPoint X x) σ))) ≫
        (SSet.chainComplexMap
          (Subcomplex.fiber (basedPathProj X x) x).ι
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).f 1) ≫
      ((basedPathEvaluationHomotopy X x).chainComplexMap
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).hom 1 2 := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let E := basedPath X x
  let F : SSet.{u} := (Subcomplex.fiber (basedPathProj X x) x).toSSet
  let ι : F ⟶ E := (Subcomplex.fiber (basedPathProj X x) x).ι
  let τ : Δ[1] ⟶ F := RelativeMorphism.map
    (ConnectingMap.connectingPtSimplexRep
      (p := basedPathProj X x) (e := basedPathPoint X x)
      (basedPathProj_basedPathPoint X x) σ)
  let ℓ : Δ[1] ⟶ E := RelativeMorphism.map
    (ConnectingMap.chosenLiftPt (e := basedPathPoint X x)
      (basedPathProj X x) (basedPathProj_basedPathPoint X x) σ)
  let K := (basedPathEvaluationHomotopy X x).chainComplexMap R
  change E.ιChainComplex (R := R) (SSet.yonedaEquiv (X := E) ℓ) ≫ K.hom 1 2 =
    (F.ιChainComplex (R := R) (SSet.yonedaEquiv (X := F) τ) ≫
      (SSet.chainComplexMap ι R).f 1) ≫ K.hom 1 2
  have hmaps : τ ≫ ι = ℓ :=
    ConnectingMap.connectingPtSimplexRep_ι (basedPathProj X x) (basedPathPoint X x)
      (basedPathProj_basedPathPoint X x) σ
  have hs : ι.app _ (SSet.yonedaEquiv (X := F) τ) =
      SSet.yonedaEquiv (X := E) ℓ :=
    (SSet.yonedaEquiv_comp τ ι).symm.trans
      (congrArg (SSet.yonedaEquiv (X := E)) hmaps)
  have hc : F.ιChainComplex (R := R) (SSet.yonedaEquiv (X := F) τ) ≫
      (SSet.chainComplexMap ι R).f 1 =
    E.ιChainComplex (R := R) (SSet.yonedaEquiv (X := E) ℓ) :=
    (SSet.ι_chainComplexMap_f (X := F) (Y := E) (f := ι) (R := R)
      (x := SSet.yonedaEquiv (X := F) τ)).trans
        (congrArg (fun s => E.ιChainComplex (R := R) s) hs)
  exact (congrArg (fun m => m ≫ K.hom 1 2) hc).symm

/-- The actual original chosen lift and source-first evaluation chain homotopy
relate the canonical pointed generator to the last-face connecting chain,
with the negative sign derived from the actual standard comm equation. -/
theorem evaluationConnectingRepresentative_chain_relation
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    X.ιChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
        (yonedaEquiv (RelativeMorphism.map σ)) -
      X.ιChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
        (yonedaEquiv (SSet.const x : Δ[2] ⟶ X)) =
      -evaluationConnectingChain X x σ -
        (((basedPath X x).ιChainComplex
            (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
            (ConnectingMap.chosenLift (e := basedPathPoint X x)
              (basedPathProj X x) (basedPathProj_basedPathPoint X x) σ) ≫
          ((basedPathEvaluationHomotopy X x).chainComplexMap
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).hom 2 3) ≫
          (X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 3 2) := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let E := basedPath X x
  let p := basedPathProj X x
  let e := basedPathPoint X x
  let hb := basedPathProj_basedPathPoint X x
  let L := ConnectingMap.chosenLift (e := e) p hb σ
  let ℓ := yonedaEquiv (RelativeMorphism.map (ConnectingMap.chosenLiftPt (e := e) p hb σ))
  let cE : E _⦋1⦌ := yonedaEquiv (SSet.const e : Δ[1] ⟶ E)
  let K := (basedPathEvaluationHomotopy X x).chainComplexMap R
  have hface (i : Fin 3) (hi : i ≠ Fin.last 2) : E.δ i L = cE := by
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      congrArg yonedaEquiv (ConnectingMap.chosenLift_face_eq_const p hb σ i hi)
  have hlast : E.δ (2 : Fin 3) L = ℓ := by
    have hi : (Fin.last 2 : Fin 3) = (2 : Fin 3) := by decide
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, hi] using
      (congrArg yonedaEquiv (ConnectingMap.chosenLift_face_eq p hb σ)).symm
  have hboundary : E.ιChainComplex (R := R) L ≫ (E.chainComplex R).d 2 1 =
      E.ιChainComplex (R := R) ℓ := by
    rw [ιChainComplex_d, Fin.sum_univ_three]
    simp [hface 0 (by decide), hface 1 (by decide), hlast]
  have hproj : p.app _ L = yonedaEquiv (RelativeMorphism.map σ) := by
    have h := congrArg yonedaEquiv (ConnectingMap.chosenLift_projects p hb σ)
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have hconst : (SSet.const x : E ⟶ X).app _ L =
      yonedaEquiv (SSet.const x : Δ[2] ⟶ X) := by
    have h := yonedaEquiv_comp (yonedaEquiv.symm L) (SSet.const x : E ⟶ X)
    simpa only [SSet.comp_const, Equiv.apply_symm_apply] using h.symm
  have hk := K.comm 2
  rw [dNext_eq K.hom (i := 2) (i' := 1) (by rfl),
    prevD_eq K.hom (j := 2) (j' := 3) (by rfl)] at hk
  have h := congrArg (fun f => E.ιChainComplex (R := R) L ≫ f) hk
  simp only [Preadditive.comp_add, ← Category.assoc] at h
  rw [ι_chainComplexMap_f, hconst, ι_chainComplexMap_f, hproj,
    hboundary] at h
  change X.ιChainComplex (R := R) (yonedaEquiv (RelativeMorphism.map σ)) -
      X.ιChainComplex (R := R) (yonedaEquiv (SSet.const x : Δ[2] ⟶ X)) =
    -(E.ιChainComplex (R := R) ℓ ≫ K.hom 1 2) -
      ((E.ιChainComplex (R := R) L ≫ K.hom 2 3) ≫ (X.chainComplex R).d 3 2)
  rw [h]
  abel

/-- The actual last-face evaluation connecting chain is a genuine cycle;
the differential vanishing is proved from the actual representative relation
and the original canonical cycle, never assumed as an input. -/
theorem evaluationConnectingRepresentative_cycle
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    evaluationConnectingChain X x σ ≫
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 2 1 = 0 := by
  have h := congrArg (fun f => f ≫
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 2 1)
    (evaluationConnectingRepresentative_chain_relation X x σ)
  rw [pointedTwoSubConstGenerator_cycle σ] at h
  simp only [Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero, sub_zero] at h
  exact neg_eq_zero.mp h.symm

/-- The actual integral cycle obtained from evaluation of the original
chosen last-face connecting representative. -/
def evaluationConnectingRepresentativeCycle
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cycles 2 :=
  (X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).liftCycles
    (evaluationConnectingChain X x σ) 1 (by simp)
      (evaluationConnectingRepresentative_cycle X x σ)

/-- Representative compatibility of the actual canonical native Hurewicz
class with the actual source-first last-face evaluation class. The minus
comes from the proved standard chain homotopy, not a sign/result premise. -/
theorem evaluationConnectingRepresentative_hurewicz_class
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    pointedTwoHomologyClass σ ≫
        (X.normalizedHomologyIso (C := AddCommGrpCat.{u})
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom =
      -(evaluationConnectingRepresentativeCycle X x σ ≫
        (X.chainComplex
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 2) := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let C := X.chainComplex R
  let z := X.ιChainComplex (R := R) (yonedaEquiv (RelativeMorphism.map σ)) -
    X.ιChainComplex (R := R) (yonedaEquiv (SSet.const x : Δ[2] ⟶ X))
  let Z := C.liftCycles z 1 (by simp) (pointedTwoSubConstGenerator_cycle σ)
  let T := evaluationConnectingRepresentativeCycle X x σ
  let B := evaluationChosenLiftChain X x σ ≫
    ((basedPathEvaluationHomotopy X x).chainComplexMap R).hom 2 3
  have hZi : Z ≫ C.iCycles 2 = z :=
    C.liftCycles_i z 1 (by simp) (pointedTwoSubConstGenerator_cycle σ)
  have hTi : T ≫ C.iCycles 2 = evaluationConnectingChain X x σ :=
    C.liftCycles_i (evaluationConnectingChain X x σ) 1 (by simp)
      (evaluationConnectingRepresentative_cycle X x σ)
  have hZT : Z = -T - (B ≫ C.toCycles 3 2) := by
    apply (cancel_mono (C.iCycles 2)).mp
    rw [Preadditive.sub_comp, Preadditive.neg_comp, hZi, hTi,
      Category.assoc, HomologicalComplex.toCycles_i]
    exact evaluationConnectingRepresentative_chain_relation X x σ
  rw [pointedTwoHomologyClass_fromNormalized_explicit]
  change Z ≫ C.homologyπ 2 = -(T ≫ C.homologyπ 2)
  rw [hZT, Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero, sub_zero]


/-!
Actual source-first evaluation chain operator restricted by the original
strict loop inclusion. Both endpoint chain maps are the same original
constant map, so the differential/operator sum vanishes with its actual sign.
-/

/-- The actual standard evaluation operator restricted by the original loop
fiber inclusion anticommutes with the original unnormalized differentials.
No cycle, homotopy, boundary-vanishing or compatibility witness is an input. -/
theorem loopEvaluationChain_anticommutes
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) :
    ((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d (n + 1) n ≫
        ((SSet.chainComplexMap (Subcomplex.fiber (basedPathProj X x) x).ι
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).f n ≫
          ((basedPathEvaluationHomotopy X x).chainComplexMap
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).hom n (n + 1)) +
      ((SSet.chainComplexMap (Subcomplex.fiber (basedPathProj X x) x).ι
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).f (n + 1) ≫
        ((basedPathEvaluationHomotopy X x).chainComplexMap
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).hom
            (n + 1) (n + 2)) ≫
        (X.chainComplex
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d
            (n + 2) (n + 1) = 0 := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let E := basedPath X x
  let F : SSet.{u} := (Subcomplex.fiber (basedPathProj X x) x).toSSet
  let j : F ⟶ E := (Subcomplex.fiber (basedPathProj X x) x).ι
  let Γ := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  have hf : SSet.chainComplexMap j R ≫
      SSet.chainComplexMap (SSet.const x : E ⟶ X) R =
        SSet.chainComplexMap (SSet.const x : F ⟶ X) R := by
    change Γ.map j ≫ Γ.map (SSet.const x : E ⟶ X) =
      Γ.map (SSet.const x : F ⟶ X)
    rw [← Functor.map_comp, SSet.comp_const]
  have hg : SSet.chainComplexMap j R ≫
      SSet.chainComplexMap (basedPathProj X x) R =
        SSet.chainComplexMap (SSet.const x : F ⟶ X) R := by
    change Γ.map j ≫ Γ.map (basedPathProj X x) =
      Γ.map (SSet.const x : F ⟶ X)
    rw [← Functor.map_comp]
    dsimp only [j]
    rw [Subcomplex.fiber_ι_comp]
  let K := (basedPathEvaluationHomotopy X x).chainComplexMap R
  let J := K.compLeft (SSet.chainComplexMap j R)
  have hk := J.comm (n + 1)
  have hfg : (SSet.chainComplexMap j R ≫
        SSet.chainComplexMap (SSet.const x : E ⟶ X) R).f (n + 1) =
      (SSet.chainComplexMap j R ≫
        SSet.chainComplexMap (basedPathProj X x) R).f (n + 1) :=
    (congrArg (fun m => m.f (n + 1)) hf).trans
      (congrArg (fun m => m.f (n + 1)) hg).symm
  have hs : dNext (n + 1) J.hom + prevD (n + 1) J.hom = 0 := by
    apply add_right_cancel
    exact (hk.symm.trans hfg).trans (zero_add _).symm
  rw [dNext_eq J.hom (i := n + 1) (i' := n) (by rfl),
    prevD_eq J.hom (j := n + 1) (j' := n + 2) (by rfl)] at hs
  change (F.chainComplex R).d (n + 1) n ≫ J.hom n (n + 1) +
    J.hom (n + 1) (n + 2) ≫ (X.chainComplex R).d (n + 2) (n + 1) = 0
  exact hs

/-!
The actual representative evaluation cycle of any original pointed strict
loop. The original two vertex faces prove the source edge cycle, and the
proved n=0 operator law proves the actual target two-cycle.
No π₁ quotient, unit/product or full π₂ comparison is asserted here.
-/

/-- Apply the original strict-loop inclusion chain map and original standard
based-path evaluation component to the original pointed loop generator. -/
def pointedLoopEvaluationChain
    (X : SSet.{u}) (x : X _⦋0⦌)
    (γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
      (Subcomplex.fiber.basePoint (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x))) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).X 2 :=
  ((Subcomplex.fiber (basedPathProj X x) x).toSSet.ιChainComplex
      (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
      (yonedaEquiv (RelativeMorphism.map γ)) ≫
    (SSet.chainComplexMap (Subcomplex.fiber (basedPathProj X x) x).ι
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).f 1) ≫
    ((basedPathEvaluationHomotopy X x).chainComplexMap
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).hom 1 2

/-- The actual evaluation chain of an original pointed strict loop is a
cycle, by its literal constant vertex faces and the actual n=0 operator law. -/
theorem pointedLoopEvaluationChain_cycle
    (X : SSet.{u}) (x : X _⦋0⦌)
    (γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
      (Subcomplex.fiber.basePoint (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x))) :
    pointedLoopEvaluationChain X x γ ≫
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 2 1 = 0 := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let F : SSet.{u} := (Subcomplex.fiber (basedPathProj X x) x).toSSet
  let b : F _⦋0⦌ := Subcomplex.fiber.basePoint (basedPathPoint X x)
    (basedPathProj_basedPathPoint X x)
  let z := yonedaEquiv (RelativeMorphism.map γ)
  have hface (i : Fin 2) : F.δ i z = yonedaEquiv (SSet.const b : Δ[0] ⟶ F) := by
    dsimp only [z]
    rw [← stdSimplex.yonedaEquiv_δ_comp, PtSimplex.δ_map]
  have hboundary : F.ιChainComplex (R := R) z ≫ (F.chainComplex R).d 1 0 = 0 := by
    rw [ιChainComplex_d, Fin.sum_univ_two]
    simp [hface]
  have h := congrArg (fun m => F.ιChainComplex (R := R) z ≫ m)
    (loopEvaluationChain_anticommutes X x 0)
  simp only [Preadditive.comp_add, comp_zero, ← Category.assoc] at h
  rw [hboundary] at h
  simp only [zero_comp, zero_add] at h
  change ((F.ιChainComplex (R := R) z ≫
      (SSet.chainComplexMap (Subcomplex.fiber (basedPathProj X x) x).ι R).f 1) ≫
    ((basedPathEvaluationHomotopy X x).chainComplexMap R).hom 1 2) ≫
      (X.chainComplex R).d 2 1 = 0
  simpa only [Category.assoc] using h

/-- The actual liftCycles of the original pointed-loop evaluation chain. -/
def pointedLoopEvaluationCycle
    (X : SSet.{u}) (x : X _⦋0⦌)
    (γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
      (Subcomplex.fiber.basePoint (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x))) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cycles 2 :=
  (X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).liftCycles
    (pointedLoopEvaluationChain X x γ) 1 (by simp)
      (pointedLoopEvaluationChain_cycle X x γ)

/-- The actual original H₂ class of the evaluation cycle, at representative
level. No π₁ quotient invariance or multiplication result is part of this definition. -/
def pointedLoopEvaluationClass
    (X : SSet.{u}) (x : X _⦋0⦌)
    (γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
      (Subcomplex.fiber.basePoint (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x))) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2 :=
  pointedLoopEvaluationCycle X x γ ≫
    (X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 2

/-!
The actual evaluation connecting lift and the actual pointed strict-loop
representative give the same original two-cycle. The original cycles inclusion
and two standard liftCycles identities reduce this to the proved chain map
characteristic, with no supplied representative/equality witness.
-/

/-- The actual last-face evaluation cycle equals the actual pointed-loop
cycle of the original connectingPtSimplexRep in the literal strict fiber. -/
theorem evaluationConnectingRepresentativeCycle_eq_pointed_loop
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (σ : X.PtSimplex 2 x) :
    evaluationConnectingRepresentativeCycle X x σ =
      pointedLoopEvaluationCycle X x
        (ConnectingMap.connectingPtSimplexRep
          (p := basedPathProj X x) (e := basedPathPoint X x)
          (basedPathProj_basedPathPoint X x) σ) := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let C := X.chainComplex R
  let γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
      (Subcomplex.fiber.basePoint (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x)) :=
    ConnectingMap.connectingPtSimplexRep
      (p := basedPathProj X x) (e := basedPathPoint X x)
      (basedPathProj_basedPathPoint X x) σ
  have hchain : evaluationConnectingChain X x σ =
      pointedLoopEvaluationChain X x γ := by
    let E : SSet.{u} := basedPath X x
    let F : SSet.{u} := (Subcomplex.fiber (basedPathProj X x) x).toSSet
    let ι : F ⟶ E := (Subcomplex.fiber (basedPathProj X x) x).ι
    let τ : Δ[1] ⟶ F := RelativeMorphism.map γ
    let ℓ : Δ[1] ⟶ E := RelativeMorphism.map
      (ConnectingMap.chosenLiftPt (e := basedPathPoint X x)
        (basedPathProj X x) (basedPathProj_basedPathPoint X x) σ)
    let K := (basedPathEvaluationHomotopy X x).chainComplexMap R
    have hmaps : τ ≫ ι = ℓ :=
      ConnectingMap.connectingPtSimplexRep_ι (basedPathProj X x) (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x) σ
    have hs : ι.app _ (SSet.yonedaEquiv (X := F) τ) =
        SSet.yonedaEquiv (X := E) ℓ :=
      (SSet.yonedaEquiv_comp τ ι).symm.trans
        (congrArg (SSet.yonedaEquiv (X := E)) hmaps)
    have hc : F.ιChainComplex (C := AddCommGrpCat.{u}) (R := R)
        (SSet.yonedaEquiv (X := F) τ) ≫
          (SSet.chainComplexMap (C := AddCommGrpCat.{u}) ι R).f 1 =
        E.ιChainComplex (C := AddCommGrpCat.{u}) (R := R)
          (SSet.yonedaEquiv (X := E) ℓ) :=
      (SSet.ι_chainComplexMap_f (C := AddCommGrpCat.{u})
        (X := F) (Y := E) (f := ι) (R := R)
        (x := SSet.yonedaEquiv (X := F) τ)).trans
          (congrArg (fun s => E.ιChainComplex (C := AddCommGrpCat.{u}) (R := R) s) hs)
    have htransport := congrArg (fun m => m ≫ K.hom 1 2) hc
    simpa only [evaluationConnectingChain, pointedLoopEvaluationChain,
      E, F, R, ι, τ, ℓ, K] using htransport.symm
  have hEi : evaluationConnectingRepresentativeCycle X x σ ≫ C.iCycles 2 =
      evaluationConnectingChain X x σ := by
    unfold evaluationConnectingRepresentativeCycle
    exact HomologicalComplex.liftCycles_i (K := C) (i := 2)
      (k := evaluationConnectingChain X x σ) (j := 1) (hj := by simp)
      (hk := evaluationConnectingRepresentative_cycle X x σ)
  have hPi : pointedLoopEvaluationCycle X x γ ≫ C.iCycles 2 =
      pointedLoopEvaluationChain X x γ := by
    unfold pointedLoopEvaluationCycle
    exact HomologicalComplex.liftCycles_i (K := C) (i := 2)
      (k := pointedLoopEvaluationChain X x γ) (j := 1) (hj := by simp)
      (hk := pointedLoopEvaluationChain_cycle X x γ)
  have hcycle : evaluationConnectingRepresentativeCycle X x σ =
      pointedLoopEvaluationCycle X x γ := by
    apply (cancel_mono (C.iCycles 2)).mp
    rw [hEi, hPi]
    exact hchain
  simpa only [γ] using hcycle


/-!
The actual original short-complex map from the strict-loop degree-one window
to the original space degree-two window. The negative outer components and
positive middle component are forced by the actual operator equations.
-/

/-- The actual strict-loop evaluation short-complex map, with components
(−J₂₃, J₁₂, −J₀₁) on the original three displayed chain objects. -/
def loopEvaluationShortComplexMap (X : SSet.{u}) (x : X _⦋0⦌) :
    ((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).sc' 2 1 0 ⟶
    (X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).sc' 3 2 1 := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let D := (Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex R
  let C := X.chainComplex R
  let j := (Subcomplex.fiber (basedPathProj X x) x).ι
  let k := (basedPathEvaluationHomotopy X x).chainComplexMap R
  refine
    { τ₁ := -((SSet.chainComplexMap j R).f 2 ≫ k.hom 2 3)
      τ₂ := (SSet.chainComplexMap j R).f 1 ≫ k.hom 1 2
      τ₃ := -((SSet.chainComplexMap j R).f 0 ≫ k.hom 0 1)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · let J₁₂ : D.X 1 ⟶ C.X 2 :=
      (SSet.chainComplexMap j R).f 1 ≫ k.hom 1 2
    let J₂₃ : D.X 2 ⟶ C.X 3 :=
      (SSet.chainComplexMap j R).f 2 ≫ k.hom 2 3
    have h : D.d 2 1 ≫ J₁₂ + J₂₃ ≫ C.d 3 2 = 0 := by
      simpa only [J₁₂, J₂₃, D, C, R, j, k] using
        (loopEvaluationChain_anticommutes X x 1)
    have hleft : (-J₂₃) ≫ C.d 3 2 = D.d 2 1 ≫ J₁₂ := by
      rw [Preadditive.neg_comp]
      apply add_right_cancel
      exact (neg_add_cancel _).trans h.symm
    simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_f,
      J₁₂, J₂₃, D, C, R, Category.assoc] using hleft
  · change ((SSet.chainComplexMap j R).f 1 ≫ k.hom 1 2) ≫ C.d 2 1 =
      D.d 1 0 ≫ (-((SSet.chainComplexMap j R).f 0 ≫ k.hom 0 1))
    rw [Preadditive.comp_neg]
    apply add_left_cancel
    exact (loopEvaluationChain_anticommutes X x 0).trans (add_neg_cancel _).symm

/-- The actual integral H₁ of the original strict loop fiber maps to H₂(X)
through the original short-complex map and standard homologyIsoSc' comparisons. -/
def loopEvaluationHomologyMap (X : SSet.{u}) (x : X _⦋0⦌) :
    (Subcomplex.fiber (basedPathProj X x) x).toSSet.homology
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 1 ⟶
      X.homology
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2 :=
  (((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyIsoSc'
      2 1 0 (by simp) (by simp)).hom ≫
  ShortComplex.homologyMap (loopEvaluationShortComplexMap X x) ≫
  ((X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyIsoSc'
      3 2 1 (by simp) (by simp)).inv

/-- The original homology projections identify this transported map with
its actual short-complex cycles map; no H₁/H₂ identification is supplied. -/
theorem loopEvaluationHomologyMap_homologyπ (X : SSet.{u}) (x : X _⦋0⦌) :
    ((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 1 ≫
      loopEvaluationHomologyMap X x =
    (((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cyclesIsoSc'
          2 1 0 (by simp) (by simp)).hom ≫
      ShortComplex.cyclesMap (loopEvaluationShortComplexMap X x) ≫
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cyclesIsoSc'
          3 2 1 (by simp) (by simp)).inv ≫
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 2 := by
  unfold loopEvaluationHomologyMap
  rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv]

/-- On the original cycles inclusion, the constructed comparison retains
exactly the positive middle evaluation component J₁₂. -/
theorem loopEvaluationHomologyMap_cycles_i (X : SSet.{u}) (x : X _⦋0⦌) :
    ((((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cyclesIsoSc'
          2 1 0 (by simp) (by simp)).hom ≫
      ShortComplex.cyclesMap (loopEvaluationShortComplexMap X x) ≫
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cyclesIsoSc'
          3 2 1 (by simp) (by simp)).inv) ≫
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 2 =
    ((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 1 ≫
      (SSet.chainComplexMap (Subcomplex.fiber (basedPathProj X x) x).ι
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).f 1 ≫
      ((basedPathEvaluationHomotopy X x).chainComplexMap
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).hom 1 2 := by
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    ShortComplex.cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]
  rfl

/-!
The actual H₁→H₂ map sends the original pointed-loop one-cycle class to the
original evaluation two-cycle class, using the existing projection/inclusion
characteristics rather than a supplied generator result.
-/

/-- The actual original H₁→H₂ map has the positive original pointed-loop
class formula on the literal one-cycle and actual homology projections. -/
theorem loopEvaluationHomologyMap_pointed_loop
    (X : SSet.{u}) (x : X _⦋0⦌)
    (γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
      (Subcomplex.fiber.basePoint (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x))) :
    (((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).liftCycles
      ((Subcomplex.fiber (basedPathProj X x) x).toSSet.ιChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
        (yonedaEquiv (RelativeMorphism.map γ)))
      0 (by simp) (by
        rw [ιChainComplex_d, Fin.sum_univ_two]
        simp only [← stdSimplex.yonedaEquiv_δ_comp, PtSimplex.δ_map]
        simp) ≫
      ((Subcomplex.fiber (basedPathProj X x) x).toSSet.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 1) ≫
      loopEvaluationHomologyMap X x = pointedLoopEvaluationClass X x γ := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let F : SSet.{u} := (Subcomplex.fiber (basedPathProj X x) x).toSSet
  let D := F.chainComplex R
  let C := X.chainComplex R
  let s := yonedaEquiv (RelativeMorphism.map γ)
  have hd : F.ιChainComplex (R := R) s ≫ D.d 1 0 = 0 := by
    rw [ιChainComplex_d, Fin.sum_univ_two]
    dsimp only [s]
    simp only [← stdSimplex.yonedaEquiv_δ_comp, PtSimplex.δ_map]
    simp
  let a : R ⟶ D.cycles 1 := D.liftCycles
    (F.ιChainComplex (R := R) s) 0 (by simp) hd
  let v : D.cycles 1 ⟶ C.cycles 2 :=
    (D.cyclesIsoSc' 2 1 0 (by simp) (by simp)).hom ≫
      ShortComplex.cyclesMap (loopEvaluationShortComplexMap X x) ≫
      (C.cyclesIsoSc' 3 2 1 (by simp) (by simp)).inv
  have hi : v ≫ C.iCycles 2 = D.iCycles 1 ≫
      (SSet.chainComplexMap (Subcomplex.fiber (basedPathProj X x) x).ι R).f 1 ≫
      ((basedPathEvaluationHomotopy X x).chainComplexMap R).hom 1 2 :=
    loopEvaluationHomologyMap_cycles_i X x
  have hAi : a ≫ D.iCycles 1 = F.ιChainComplex (R := R) s := by
    dsimp only [a]
    exact HomologicalComplex.liftCycles_i (K := D) (i := 1)
      (k := F.ιChainComplex (R := R) s) (j := 0) (hj := by simp) (hk := hd)
  have hTi : pointedLoopEvaluationCycle X x γ ≫ C.iCycles 2 =
      pointedLoopEvaluationChain X x γ := by
    unfold pointedLoopEvaluationCycle
    exact HomologicalComplex.liftCycles_i (K := C) (i := 2)
      (k := pointedLoopEvaluationChain X x γ) (j := 1) (hj := by simp)
      (hk := pointedLoopEvaluationChain_cycle X x γ)
  have ha : a ≫ v = pointedLoopEvaluationCycle X x γ := by
    apply (cancel_mono (C.iCycles 2)).mp
    rw [Category.assoc, hi, hTi, ← Category.assoc, hAi]
    simp only [pointedLoopEvaluationChain, F, R, s, Category.assoc]
  have hπ : D.homologyπ 1 ≫ loopEvaluationHomologyMap X x =
      v ≫ C.homologyπ 2 := by
    simpa only [v, D, C, R, Category.assoc] using
      (loopEvaluationHomologyMap_homologyπ X x)
  have hclass : (a ≫ D.homologyπ 1) ≫ loopEvaluationHomologyMap X x =
      pointedLoopEvaluationClass X x γ := by
    rw [Category.assoc, hπ, ← Category.assoc, ha]
    rfl
  simpa only [a, D, F, R, s] using hclass

/-!
The actual native-π₁ / H₁ / H₂ composite at the literal original strict fiber
and original point, followed by its inverse-edge generator formula.
-/

/-- Compose the actual native π₁ multiplicative comparison, the existing
fundamental-group H₁ forward map, and the constructed original H₁→H₂ map. -/
def nativeLoopHomologyCompositeMulHom
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    KanComplex.π 1 (Subcomplex.fiber (basedPathProj X x) x).toSSet
        (Subcomplex.fiber.basePoint (basedPathPoint X x)
          (basedPathProj_basedPathPoint X x)) →*
      Multiplicative
        (↑(X.homology (C := AddCommGrpCat.{u})
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2) : Type u) := by
  let F : SSet.{u} := (Subcomplex.fiber (basedPathProj X x) x).toSSet
  let b : F _⦋0⦌ := Subcomplex.fiber.basePoint (basedPathPoint X x)
    (basedPathProj_basedPathPoint X x)
  exact (loopEvaluationHomologyMap X x).hom.toMultiplicative.comp
    ((fundamentalGroupHomologyOneHom F b).comp
      (KanComplex.piOneMulEquivFundamentalGroupoidEnd (X := F) b).toMonoidHom)

/-!
The actual native-loop composite has the negative original pointed-generator
formula. The sign comes from the existing inverse fundamental edge, actual
public H₁ characteristic and genuine positive H₁→H₂ class equation.
-/

/-- The actual native-loop composite sends the original pointed loop to
minus its actual original evaluation two-cycle class. -/
theorem nativeLoopHomologyCompositeMulHom_pointed_loop
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌)
    (γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
      (Subcomplex.fiber.basePoint (basedPathPoint X x)
        (basedPathProj_basedPathPoint X x))) :
    nativeLoopHomologyCompositeMulHom X x (KanComplex.π.mk γ) =
      Multiplicative.ofAdd
        (-(pointedLoopEvaluationClass X x γ (ULift.up (1 : ℤ)))) := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let F : SSet.{u} := (Subcomplex.fiber (basedPathProj X x) x).toSSet
  let b : F _⦋0⦌ := Subcomplex.fiber.basePoint (basedPathPoint X x)
    (basedPathProj_basedPathPoint X x)
  let D := F.chainComplex R
  let s : F _⦋1⦌ := SSet.yonedaEquiv (X := F) (RelativeMorphism.map γ)
  let e : F.Edge b b := Edge.mk s
    (by dsimp only [s, b]; simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
    (by dsimp only [s, b]; simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
  have hd : F.ιChainComplex (R := R) e.edge ≫ D.d 1 0 = 0 := by
    rw [ιChainComplex_d, Fin.sum_univ_two]
    simp [e.tgt_eq, e.src_eq]
  let a : R ⟶ D.cycles 1 := D.liftCycles
    (F.ιChainComplex (R := R) e.edge) 0 (by simp) hd
  let u : (↑(F.homology (C := AddCommGrpCat.{u}) R 1) : Type u) :=
    (a ≫ D.homologyπ 1) (ULift.up (1 : ℤ))
  have hEnd : KanComplex.piOneMulEquivFundamentalGroupoidEnd (X := F) b
      (KanComplex.π.mk γ) =
        End.of (CategoryTheory.inv (FundamentalGroupoid.homMk e)) := by
    simpa only [e, s, b] using
      (KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk (X := F) b γ)
  have hH1 : fundamentalGroupHomologyOneHom F b
      (End.of (CategoryTheory.inv (FundamentalGroupoid.homMk e))) =
        Multiplicative.ofAdd (-u) := by
    simpa only [u, a, D, R] using
      (fundamentalGroupHomologyOneHom_inv_homMk F b e)
  have hmap : (a ≫ D.homologyπ 1) ≫ loopEvaluationHomologyMap X x =
      pointedLoopEvaluationClass X x γ := by
    simpa only [a, D, F, R, e, s, Edge.mk_edge] using
      (loopEvaluationHomologyMap_pointed_loop X x γ)
  have hvalue : (loopEvaluationHomologyMap X x).hom u =
      pointedLoopEvaluationClass X x γ (ULift.up (1 : ℤ)) :=
    ConcreteCategory.congr_hom hmap (ULift.up (1 : ℤ))
  have hcomp : nativeLoopHomologyCompositeMulHom X x (KanComplex.π.mk γ) =
      (loopEvaluationHomologyMap X x).hom.toMultiplicative
        (fundamentalGroupHomologyOneHom F b
          (KanComplex.piOneMulEquivFundamentalGroupoidEnd
            (X := F) b (KanComplex.π.mk γ))) := by
    rfl
  rw [hcomp, hEnd, hH1]
  apply Multiplicative.toAdd.injective
  change (loopEvaluationHomologyMap X x).hom (-u) =
    -(pointedLoopEvaluationClass X x γ (ULift.up (1 : ℤ)))
  rw [map_neg]
  exact congrArg Neg.neg hvalue

/-- The actual normalized native degree-two Hurewicz map, included in raw
H₂, equals the original connecting map followed by actual loop homology. -/
theorem degreeTwoHurewiczElementMulHom_loop_homology
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) (a : KanComplex.π 2 X x) :
    (X.normalizedHomologyIso (C := AddCommGrpCat.{u})
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom
        (Multiplicative.toAdd (degreeTwoHurewiczElementMulHom x a)) =
      Multiplicative.toAdd
        (nativeLoopHomologyCompositeMulHom X x
          ((loopFibrationSequence X x).connectingMap 1 a)) := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let ρ : (X.normalizedChainComplex (C := AddCommGrpCat.{u}) R).homology 2 ⟶
      X.homology (C := AddCommGrpCat.{u}) R 2 :=
    (X.normalizedHomologyIso (C := AddCommGrpCat.{u}) R 2).hom
  induction a using KanComplex.π.rec with
  | mk σ =>
    let γ : (Subcomplex.fiber (basedPathProj X x) x).toSSet.PtSimplex 1
        (Subcomplex.fiber.basePoint (basedPathPoint X x)
          (basedPathProj_basedPathPoint X x)) :=
      @ConnectingMap.connectingPtSimplexRep (basedPath X x) X 1
        (basedPathProj X x) (basedPathPoint X x) x
        (basedPathProj_basedPathPoint X x) (loopFibrationSequence X x).fibration_p σ
    have hδ : (loopFibrationSequence X x).connectingMap 1 (KanComplex.π.mk σ) =
        KanComplex.π.mk γ := by
      simpa only [γ, loopFibrationSequence] using
        (FibrationSequence.connectingMap_mk (n := 1) (loopFibrationSequence X x) σ)
    have hγ : evaluationConnectingRepresentativeCycle X x σ =
        pointedLoopEvaluationCycle X x γ := by
      simpa only [γ, loopFibrationSequence] using
        (evaluationConnectingRepresentativeCycle_eq_pointed_loop X x σ)
    have hm : pointedTwoHomologyClass σ ≫ ρ =
        -(pointedLoopEvaluationClass X x γ) := by
      have h := evaluationConnectingRepresentative_hurewicz_class X x σ
      rw [hγ] at h
      simpa only [ρ, R, pointedLoopEvaluationClass] using h
    have hv : ρ (pointedTwoHomologyClass σ (ULift.up (1 : ℤ))) =
        -(pointedLoopEvaluationClass X x γ (ULift.up (1 : ℤ))) :=
      ConcreteCategory.congr_hom hm (ULift.up (1 : ℤ))
    have hright : Multiplicative.toAdd
        (nativeLoopHomologyCompositeMulHom X x
          ((loopFibrationSequence X x).connectingMap 1 (KanComplex.π.mk σ))) =
        Multiplicative.toAdd (nativeLoopHomologyCompositeMulHom X x (KanComplex.π.mk γ)) :=
      congrArg (fun z : KanComplex.π 1
        (Subcomplex.fiber (basedPathProj X x) x).toSSet
          (Subcomplex.fiber.basePoint (basedPathPoint X x)
            (basedPathProj_basedPathPoint X x)) =>
        Multiplicative.toAdd (nativeLoopHomologyCompositeMulHom X x z)) hδ
    have hgen : Multiplicative.toAdd
        (nativeLoopHomologyCompositeMulHom X x (KanComplex.π.mk γ)) =
        -(pointedLoopEvaluationClass X x γ (ULift.up (1 : ℤ))) := by
      simpa only [_root_.toAdd_ofAdd] using
        (congrArg Multiplicative.toAdd
          (nativeLoopHomologyCompositeMulHom_pointed_loop X x γ))
    have hleft : (X.normalizedHomologyIso (C := AddCommGrpCat.{u})
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom
        (Multiplicative.toAdd (degreeTwoHurewiczElementMulHom x (KanComplex.π.mk σ))) =
        -(pointedLoopEvaluationClass X x γ (ULift.up (1 : ℤ))) := by
      rw [degreeTwoHurewiczElementMulHom_mk]
      simpa only [_root_.toAdd_ofAdd, R, ρ] using hv
    exact hleft.trans (hright.trans hgen).symm


end SSet
