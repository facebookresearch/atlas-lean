/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseChangeDeck
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeNerveUnitComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexFibrationTransitions
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularPathDeckNaturality
public import MathlibExt.CategoryTheory.CategoryHomology.InvertingCoefficientCoinvariants
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
public import MathlibExt.CategoryTheory.CategoryHomology.ClassifyingSpaceSingular
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Actual simplex fibers and the pulled native-cover homology cocone

The original lift of each represented simplex gives a map from its actual
fiber to the original pulled native cover. Its square is a pullback, so
the map is weak over a groupoid nerve. The existing first-path coordinates
prove that any two lifts differ by the SAME inverse-precomposition deck
action. Identity of that actual deck action on homology therefore makes
the homology map independent of every lift choice.

Arbitrary actual lift choices consequently give a natural homology
cocone with invertible components. The existing computed coefficient
root-action invariance of cocones then forces the original fiber
coefficient action to be trivial. The H-space consumer derives the deck
identity from the original unit traces, not from a monodromy witness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology
  HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet.KanComplex

/-- The original simplex lift determines both coordinates of this map to the pulled cover. -/
def simplexLiftToPulledCover {B E : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ B)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = σ}) :
    pullback p σ ⟶ pullback p (nativeCoverProjection B b) :=
  pullback.lift (pullback.fst p σ) (pullback.snd p σ ≫ L.val) (by
    exact (pullback.condition (f := p) (g := σ)).trans
      ((congrArg (fun k => pullback.snd p σ ≫ k) L.property.symm).trans
        (Category.assoc (pullback.snd p σ) L.val (nativeCoverProjection B b)).symm))

/-- The original total-space projection is retained. -/
theorem simplexLiftToPulledCover_fst {B E : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ B)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = σ}) :
    simplexLiftToPulledCover p b σ L ≫ pullback.fst p (nativeCoverProjection B b) =
      pullback.fst p σ := pullback.lift_fst _ _ _

/-- The whole cover coordinate is the original represented simplex lift. -/
theorem simplexLiftToPulledCover_snd {B E : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ B)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = σ}) :
    simplexLiftToPulledCover p b σ L ≫ pullback.snd p (nativeCoverProjection B b) =
      pullback.snd p σ ≫ L.val := pullback.lift_snd _ _ _

/-- The SAME lift retains the full original pair-map square on the two pulled covers. -/
theorem simplexLiftToPulledCover_pairMap {E E' B : SSet.{u}}
    {p : E ⟶ B} {q : E' ⟶ B} (v : E ⟶ E') (hv : v ≫ q = p) (b : B _⦋0⦌)
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ B)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = σ}) :
    (simplexPullbackDiagramMap v hv).app (CostructuredArrow.mk σ) ≫
        simplexLiftToPulledCover q b σ L =
      simplexLiftToPulledCover p b σ L ≫ nativeCoverBaseChangeMap v hv b := by
  let i : SimplexIndex B := CostructuredArrow.mk σ
  let a := (simplexPullbackDiagramMap v hv).app i
  let jp := simplexLiftToPulledCover p b σ L
  let jq := simplexLiftToPulledCover q b σ L
  let c := nativeCoverBaseChangeMap v hv b
  let fp := pullback.fst p (nativeCoverProjection B b)
  let fq := pullback.fst q (nativeCoverProjection B b)
  let sp := pullback.snd p (nativeCoverProjection B b)
  let sq := pullback.snd q (nativeCoverProjection B b)
  apply pullback.hom_ext
  · have hL := (Category.assoc a jq fq).trans
      ((congrArg (fun k => a ≫ k) (simplexLiftToPulledCover_fst q b σ L)).trans
        (simplexPullbackDiagramMap_app_fst v hv i))
    have hR := (Category.assoc jp c fq).trans
      ((congrArg (fun k => jp ≫ k) (nativeCoverBaseChangeMap_fst v hv b)).trans
        ((Category.assoc jp fp v).symm.trans
          (congrArg (fun k => k ≫ v) (simplexLiftToPulledCover_fst p b σ L))))
    exact hL.trans hR.symm
  · have hL := (Category.assoc a jq sq).trans
      ((congrArg (fun k => a ≫ k) (simplexLiftToPulledCover_snd q b σ L)).trans
        ((Category.assoc a (pullback.snd q σ) L.val).symm.trans
          (congrArg (fun k => k ≫ L.val) (simplexPullbackDiagramMap_app_snd v hv i))))
    have hR := (Category.assoc jp c sq).trans
      ((congrArg (fun k => jp ≫ k) (nativeCoverBaseChangeMap_snd v hv b)).trans
        (simplexLiftToPulledCover_snd p b σ L))
    exact hL.trans hR.symm


/-- This is the actual pullback of the SAME original simplex lift. -/
theorem simplexLiftToPulledCover_isPullback {B E : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ B)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = σ}) :
    IsPullback (simplexLiftToPulledCover p b σ L) (pullback.snd p σ)
      (pullback.snd p (nativeCoverProjection B b)) L.val := by
  have hOuter : IsPullback
      (simplexLiftToPulledCover p b σ L ≫ pullback.fst p (nativeCoverProjection B b))
      (pullback.snd p σ) p (L.val ≫ nativeCoverProjection B b) := by
    rw [simplexLiftToPulledCover_fst, L.property]
    exact IsPullback.of_hasPullback p σ
  exact hOuter.of_right (simplexLiftToPulledCover_snd p b σ L)
    (IsPullback.of_hasPullback p (nativeCoverProjection B b))

/-- The original path coordinates derive transitivity of the actual inverse-precomposition
action. -/
theorem nativeSimplexLifts_exists_deck {B : SSet.{u}} [SSet.KanComplex B]
    (b : B _⦋0⦌) {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ B)
    (L K : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = σ}) :
    ∃ g : End (SSet.FundamentalGroupoid.mk b), nativeCoverDeckedSimplexLift b g σ L = K := by
  let e := nativeCoverSimplexFiberPathEquiv (X := B) (x := b) σ
  let γ := e L
  let η := e K
  let a : End (SSet.FundamentalGroupoid.mk b) := End.of (η ≫ inv γ)
  let g := a⁻¹
  have hInv : (g⁻¹).asHom = η ≫ inv γ :=
    congrArg (fun k : End (SSet.FundamentalGroupoid.mk b) => k.asHom) (inv_inv a)
  have hPath : (g⁻¹).asHom ≫ γ = η :=
    (congrArg (fun k => k ≫ γ) hInv).trans
      ((Category.assoc η (inv γ) γ).trans
        ((congrArg (fun k => η ≫ k) (IsIso.inv_hom_id γ)).trans (Category.comp_id η)))
  exact ⟨g, e.injective ((nativeCoverSimplexFiberPathEquiv_deck b g σ L).trans hPath)⟩

/-- The actual map follows the original deck action on the complete lift. -/
theorem simplexLiftToPulledCover_deck {B E : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk b)) {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ B)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = σ}) :
    simplexLiftToPulledCover p b σ L ≫ nativeCoverBaseChangeDeckMap p b g =
      simplexLiftToPulledCover p b σ (nativeCoverDeckedSimplexLift b g σ L) := by
  let j := simplexLiftToPulledCover p b σ L
  let d := nativeCoverBaseChangeDeckMap p b g
  let Lg := nativeCoverDeckedSimplexLift b g σ L
  apply pullback.hom_ext
  · exact (Category.assoc j d (pullback.fst p (nativeCoverProjection B b))).trans
      ((congrArg (fun k => j ≫ k) (nativeCoverBaseChangeDeckMap_fst p b g)).trans
        ((simplexLiftToPulledCover_fst p b σ L).trans
          (simplexLiftToPulledCover_fst p b σ Lg).symm))
  · exact (Category.assoc j d (pullback.snd p (nativeCoverProjection B b))).trans
      ((congrArg (fun k => j ≫ k) (nativeCoverBaseChangeDeckMap_snd p b g)).trans
        ((Category.assoc j (pullback.snd p (nativeCoverProjection B b))
          (nativeCoverDeckMap g)).symm.trans
          ((congrArg (fun k => k ≫ nativeCoverDeckMap g)
            (simplexLiftToPulledCover_snd p b σ L)).trans
            ((Category.assoc (pullback.snd p σ) L.val (nativeCoverDeckMap g)).trans
              ((congrArg (fun k => pullback.snd p σ ≫ k)
                (nativeCoverDeckedSimplexLift_val b g σ L).symm).trans
                (simplexLiftToPulledCover_snd p b σ Lg).symm)))))

/-- The original lift restriction gives the full original simplex-transition square. -/
theorem simplexLiftToPulledCover_transition {B E : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {s t : SSet.SimplexIndex B} (a : s ⟶ t)
    (L : {L : (SSet.stdSimplex.obj t.left : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = t.hom}) :
    (simplexPullbackDiagram p).map a ≫ simplexLiftToPulledCover p b t.hom L =
      simplexLiftToPulledCover p b s.hom
        ⟨SSet.stdSimplex.map a.left ≫ L.val, (Category.assoc _ _ _).trans
          ((congrArg (fun k => SSet.stdSimplex.map a.left ≫ k) L.property).trans
            (CostructuredArrow.w a))⟩ := by
  let Ls : {L : (SSet.stdSimplex.obj s.left : SSet.{u}) ⟶ nativeCover B b //
      L ≫ nativeCoverProjection B b = s.hom} :=
    ⟨SSet.stdSimplex.map a.left ≫ L.val, (Category.assoc _ _ _).trans
      ((congrArg (fun k => SSet.stdSimplex.map a.left ≫ k) L.property).trans
        (CostructuredArrow.w a))⟩
  change (simplexPullbackDiagram p).map a ≫ simplexLiftToPulledCover p b t.hom L =
    simplexLiftToPulledCover p b s.hom Ls
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (simplexPullbackDiagram p).map a ≫ k)
        (simplexLiftToPulledCover_fst p b t.hom L)).trans
        ((simplexPullbackDiagram_map_fst p a).trans
          (simplexLiftToPulledCover_fst p b s.hom Ls).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (simplexPullbackDiagram p).map a ≫ k)
        (simplexLiftToPulledCover_snd p b t.hom L)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ L.val) (simplexPullbackDiagram_map_snd p a)).trans
            ((Category.assoc _ _ _).trans
              (simplexLiftToPulledCover_snd p b s.hom Ls).symm))))

end SSet.KanComplex

namespace SSet

variable (G : Type u) [Groupoid.{u} G] [CategoryTheory.IsConnected G]
  {E : SSet.{u}} (p : E ⟶ CategoryTheory.nerve G)
  (b : (CategoryTheory.nerve G) _⦋0⦌) (R : AddCommGrpCat.{u}) (n : ℕ)

/-- The actual coefficient functor, using the original simplex fibers and ordinary homology. -/
abbrev simplexFibrationHomologyCoefficients : SimplexIndex (CategoryTheory.nerve G) ⥤
    AddCommGrpCat.{u} := simplexPullbackDiagram p ⋙ SSet.homologyFunctor R n

private def chosenNativeSimplexLift (s : SimplexIndex (CategoryTheory.nerve G)) :
    {L : (SSet.stdSimplex.obj s.left : SSet.{u}) ⟶
        KanComplex.nativeCover (CategoryTheory.nerve G) b //
      L ≫ KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b = s.hom} := by
  classical
  let B := CategoryTheory.nerve G
  let : B.IsConnected := CategoryTheory.nerve_isConnected_of_category_isConnected
  let : CategoryTheory.IsConnected (SSet.FundamentalGroupoid B) :=
    fundamentalGroupoid_category_isConnected B
  exact (KanComplex.nativeCoverSimplexFiberPathEquiv (X := B) (x := b) s.hom).symm
    (Classical.arbitrary _)

omit [CategoryTheory.IsConnected G] in
/-- Derived deck identity makes the actual fiber-to-cover homology map independent of EVERY lift. -/
theorem simplexLiftToPulledCover_homologyMap_independent
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ CategoryTheory.nerve G)
    (L K : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶
      KanComplex.nativeCover (CategoryTheory.nerve G) b //
      L ≫ KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b = σ})
    (hDeck : ∀ g : End (SSet.FundamentalGroupoid.mk b),
      SSet.homologyMap (KanComplex.nativeCoverBaseChangeDeckMap p b g) R n = 𝟙 _) :
    SSet.homologyMap (KanComplex.simplexLiftToPulledCover p b σ L) R n =
      SSet.homologyMap (KanComplex.simplexLiftToPulledCover p b σ K) R n := by
  let : SSet.KanComplex (CategoryTheory.nerve G) := SSet.kanComplex_nerve_of_groupoid G
  obtain ⟨g, hg⟩ := KanComplex.nativeSimplexLifts_exists_deck b σ L K
  let H := SSet.homologyFunctor R n
  have h := (H.map_comp _ _).symm.trans
    (congrArg H.map (KanComplex.simplexLiftToPulledCover_deck p b g σ L))
  have hK := congrArg (fun T => H.map (KanComplex.simplexLiftToPulledCover p b σ T)) hg
  exact (Category.comp_id _).symm.trans
    ((congrArg (fun k => H.map (KanComplex.simplexLiftToPulledCover p b σ L) ≫ k)
      (hDeck g).symm).trans (h.trans hK))

/-- Actual lift choices give a natural homology cocone; no cocone is supplied. -/
def simplexPulledCoverHomologyCocone
    (hDeck : ∀ g : End (SSet.FundamentalGroupoid.mk b),
      SSet.homologyMap (KanComplex.nativeCoverBaseChangeDeckMap p b g) R n = 𝟙 _) :
    Cocone (simplexFibrationHomologyCoefficients G p R n) where
  pt := (SSet.homologyFunctor R n).obj
    (pullback p (KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b))
  ι :=
    { app s := SSet.homologyMap
        (KanComplex.simplexLiftToPulledCover p b s.hom (chosenNativeSimplexLift G b s)) R n
      naturality {s t} a := by
        let H := SSet.homologyFunctor R n
        let Lt : {L : (SSet.stdSimplex.obj t.left : SSet.{u}) ⟶
            KanComplex.nativeCover (CategoryTheory.nerve G) b //
            L ≫ KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b = t.hom} :=
          chosenNativeSimplexLift G b t
        let Ls : {L : (SSet.stdSimplex.obj s.left : SSet.{u}) ⟶
            KanComplex.nativeCover (CategoryTheory.nerve G) b //
            L ≫ KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b = s.hom} :=
          chosenNativeSimplexLift G b s
        let La : {L : (SSet.stdSimplex.obj s.left : SSet.{u}) ⟶
            KanComplex.nativeCover (CategoryTheory.nerve G) b //
            L ≫ KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b = s.hom} :=
          ⟨SSet.stdSimplex.map a.left ≫ Lt.val,
          (Category.assoc _ _ _).trans
            ((congrArg (fun k => SSet.stdSimplex.map a.left ≫ k) Lt.property).trans
              (CostructuredArrow.w a))⟩
        have h := (H.map_comp _ _).symm.trans
          (congrArg H.map (KanComplex.simplexLiftToPulledCover_transition p b a Lt))
        have hI := simplexLiftToPulledCover_homologyMap_independent G p b R n s.hom
          La Ls hDeck
        exact h.trans (hI.trans (Category.comp_id _).symm) }

variable [Fibration p]

omit [CategoryTheory.IsConnected G] in
/-- Over the actual groupoid nerve, each original fiber-to-pulled-cover map is derived weak. -/
theorem simplexLiftToPulledCover_mem_realizationWeakEquivalences
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ CategoryTheory.nerve G)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶
      KanComplex.nativeCover (CategoryTheory.nerve G) b //
      L ≫ KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b = σ}) :
    SSet.realizationWeakEquivalences (KanComplex.simplexLiftToPulledCover p b σ L) := by
  let t := SSet.stdSimplex.isTerminalObj₀.from
    (KanComplex.nativeCover (CategoryTheory.nerve G) b)
  have ht := KanComplex.nativeCover_nerve_to_point_mem_realizationWeakEquivalences G b
  have hFac : L.val ≫ t = SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj A) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hComp : SSet.realizationWeakEquivalences (L.val ≫ t) :=
    hFac.symm ▸ stdSimplex_to_point_mem_realizationWeakEquivalences A
  let : WeakEquivalence L.val := (weakEquivalence_iff _).mpr
    (SSet.realizationWeakEquivalences.of_postcomp L.val t ht hComp)
  let : Fibration (pullback.snd p
      (KanComplex.nativeCoverProjection (CategoryTheory.nerve G) b)) :=
    SSet.fibration_of_isPullback
      (IsPullback.of_hasPullback p (KanComplex.nativeCoverProjection
          (CategoryTheory.nerve G) b)).flip
  exact (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback
      (KanComplex.simplexLiftToPulledCover_isPullback p b σ L).flip)

/-- Every component of the computed cocone is an actual homology isomorphism. -/
theorem simplexPulledCoverHomologyCocone_ι_isIso
    (hDeck : ∀ g : End (SSet.FundamentalGroupoid.mk b),
      SSet.homologyMap (KanComplex.nativeCoverBaseChangeDeckMap p b g) R n = 𝟙 _)
    (s : SimplexIndex (CategoryTheory.nerve G)) :
    IsIso ((simplexPulledCoverHomologyCocone G p b R n hDeck).ι.app s) := by
  let L := chosenNativeSimplexLift G b s
  let j := KanComplex.simplexLiftToPulledCover p b s.hom L
  have hWeak := simplexLiftToPulledCover_mem_realizationWeakEquivalences G p b s.hom L
  let : QuasiIso (SSet.chainComplexMap j R) := hWeak.quasiIso_chainComplexMap_addCommGrp R
  change IsIso (SSet.homologyMap j R n)
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap (SSet.chainComplexMap j R) n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap j R) n)

omit [CategoryTheory.IsConnected G] in
/-- The actual fibration derives inversion of every original homology coefficient transition. -/
theorem simplexFibrationHomologyCoefficients_map_isIso
    {s t : SimplexIndex (CategoryTheory.nerve G)} (a : s ⟶ t) :
    IsIso ((simplexFibrationHomologyCoefficients G p R n).map a) := by
  have hWeak := simplexPullbackTransition_mem_realizationWeakEquivalences p a
  let : QuasiIso (SSet.chainComplexMap ((simplexPullbackDiagram p).map a) R) :=
    hWeak.quasiIso_chainComplexMap_addCommGrp R
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap
    (SSet.chainComplexMap ((simplexPullbackDiagram p).map a) R) n).mp
      (inferInstance : QuasiIsoAt
        (SSet.chainComplexMap ((simplexPullbackDiagram p).map a) R) n)

section ActualRoot

variable [∀ {s t : SimplexIndex (CategoryTheory.nerve G)} (a : s ⟶ t),
  IsIso ((simplexFibrationHomologyCoefficients G p R n).map a)]

/-- The computed ACTUAL coefficient action is trivial, from actual lift independence
and the invertible original cocone component. -/
theorem simplexFibrationRootAction_isTrivial
    (hDeck : ∀ g : End (SSet.FundamentalGroupoid.mk b),
      SSet.homologyMap (KanComplex.nativeCoverBaseChangeDeckMap p b g) R n = 𝟙 _)
    (s : SimplexIndex (CategoryTheory.nerve G)) :
    Representation.IsTrivial (invertingCoefficientRootAction
      (simplexFibrationHomologyCoefficients G p R n) s) := by
  let M := simplexFibrationHomologyCoefficients G p R n
  let c := simplexPulledCoverHomologyCocone G p b R n hDeck
  let : IsIso (c.ι.app s) := simplexPulledCoverHomologyCocone_ι_isIso G p b R n hDeck s
  constructor
  intro g
  apply LinearMap.ext
  intro v
  apply (AddCommGrpCat.mono_iff_injective (c.ι.app s)).mp inferInstance
  have h := invertingCoefficientRootAction_cocone_invariant M c s g
  exact DFunLike.congr_fun h v

end ActualRoot

end SSet
