/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelCofibrationHomotopyExtension
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.ArbitraryRightSmash
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OmegaTestHomotopyCofiberClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricStableSmashCellular
import MathlibExt.CategoryTheory.Enriched.PointwiseSizeInstances
import MathlibExt.CategoryTheory.Monoidal.FiniteCube
import MathlibExt.CategoryTheory.Monoidal.MonoidWordPushoutEndpoint
import MathlibExt.CategoryTheory.Operad.Tensor.EnvelopingOrbitCells
import MathlibExt.CategoryTheory.SmallObject.Closure
import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingInstances
import MathlibExt.Topology.Category.PointedCGWH.FiniteOrbitClosedEmbedding

/-!
# Closed native cell histories

The original native smash preserves all-target based homotopy extension.
The original interval comparison then proves that each evaluated map is a
closed inclusion. In particular, a native cofibration tensored with an
arbitrary original coefficient has closed evaluated maps. The finite
pushout products use the already constructed native model and its actual
generator product comparisons.

This supplies the closed-inclusion closure used in Pavlov--Scholbach,
*Homotopy theory of symmetric powers*, §7.5, and *Symmetric operads in
abstract symmetric spectra*, Appendix 9.3.
-/

set_option autoImplicit false
noncomputable section

universe u v w uC vC wC
open CategoryTheory Limits MonoidalCategory Topology HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

section OriginalWordArrowTransport

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HC : HasColimitsOfSize.{wC, wC} C]

local instance genericWordSmallColimits : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink.{0, 0} C

private theorem originalWordBoundaryTransport (P : MorphismProperty C) [P.RespectsIso]
    (A : Mon C) {K L : C} (f : K ⟶ L) (n : ℕ)
    (h : P ((FiniteCube.iteratedPushoutProduct (fun _ : Fin n => f)).hom ▷
      FiniteCube.coefficientObj (fun _ : Fin (n + 1) => A.X))) :
    P (FiniteCube.boundaryToTop (MonoidalCategory.MonoidWordPushout.wordCube A f n)) := by
  apply (P.arrow_mk_iso_iff
    (MonoidalCategory.MonoidWordPushout.wordAttachingPushoutProductIso A f n)).mpr
  exact h

end OriginalWordArrowTransport

namespace PointedCGWH.NativeClosedCellHistory

/-- The original pointed symmetric spectrum category on its genuine operator index. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- Closedness is tested on every original operator value of the same native map. -/
def closedInclusions : MorphismProperty Carrier.{u, v} :=
  fun _ _ f => ∀ a : SymmetricOperatorIndex.{u, v},
    IsClosedEmbedding (ConcreteCategory.hom (component f a).right)

/-- The actual pointed closed-inclusion property used in every evaluation. -/
abbrev pointedClosedInclusions : MorphismProperty PointedCGWH.{u, v} :=
  TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)

instance closedInclusions_respectsIso : closedInclusions.{u, v}.RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    intro f g e hf a
    exact (pointedClosedInclusions.arrow_iso_iff
      ((evaluation (V := PointedCGWH.{u, v}) a).mapArrow.mapIso e)).mp (hf a))

instance closedInclusions_isStableUnderCobaseChange :
    closedInclusions.{u, v}.IsStableUnderCobaseChange where
  of_isPushout sq hf a :=
    pointedClosedInclusions.of_isPushout
      (sq.map (evaluation (V := PointedCGWH.{u, v}) a)) (hf a)

instance closedInclusions_isStableUnderRetracts : closedInclusions.{u, v}.IsStableUnderRetracts where
  of_retract h hg a :=
    pointedClosedInclusions.of_retract
      (h.map (evaluation (V := PointedCGWH.{u, v}) a)) (hg a)

instance closedInclusions_isStableUnderCoproducts :
    closedInclusions.{u, v}.IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape J :=
    { condition := by
        intro F₁ F₂ c₁ c₂ hc₁ hc₂ p hp m hm a
        let E := evaluation (V := PointedCGWH.{u, v}) a
        exact MorphismProperty.IsStableUnderColimitsOfShape.condition
          (W := pointedClosedInclusions) (F₁ ⋙ E) (F₂ ⋙ E)
          (E.mapCocone c₁) (E.mapCocone c₂)
          (isColimitOfPreserves E hc₁) (isColimitOfPreserves E hc₂)
          (Functor.whiskerRight p E) (fun j => hp j a) (E.map m) (by
            intro j
            exact (E.map_comp _ _).symm.trans
              ((E.congr_map (hm j)).trans (E.map_comp _ _))) }

instance closedInclusions_isStableUnderTransfiniteComposition :
    closedInclusions.{u, v}.IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape J :=
    { le := by
        rintro X Y f ⟨c⟩ a
        let E := evaluation (V := PointedCGWH.{u, v}) a
        let _ : PreservesWellOrderContinuousOfShape J E :=
          { preservesColimitsOfShape := fun _ _ => inferInstance }
        let ce : pointedClosedInclusions.TransfiniteCompositionOfShape J (E.map f) :=
          { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map E
            map_mem j hj := c.map_mem j hj a }
        exact pointedClosedInclusions.transfiniteCompositionsOfShape_le J _ ce.mem }

/-- The original continuous native history retains every closed transition and endpoint. -/
theorem transfiniteClosed
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {X Y : Carrier.{u, v}} {f : X ⟶ Y}
    (c : closedInclusions.TransfiniteCompositionOfShape J f) :
    closedInclusions f ∧ ∀ ⦃i j⦄ (φ : i ⟶ j), closedInclusions (c.F.map φ) :=
  ⟨closedInclusions.transfiniteCompositionsOfShape_le J _ c.mem, fun _ _ φ => c.mem_map φ⟩

private instance nativeClosedSmallTransfinite :
    closedInclusions.{u, v}.IsStableUnderTransfiniteComposition.{0} :=
  MorphismProperty.IsStableUnderTransfiniteComposition.shrink₀ _

section NativeCofibrations

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual native cofibration has closed inclusions in all its original levels. -/
theorem cofibrationClosed {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : cofibrations Carrier.{u, v} f) : closedInclusions f := by
  intro a
  exact Spectra.NativeOmegaWeakClosure.nativeHEP_component_closed f
    (Spectra.OriginalMonoidHEPClosure.nativeCofibrations_le_basedHEP f hf) a

/-- Right tensoring a native cofibration by any original spectrum preserves evaluated closedness. -/
theorem rightTensorClosed {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : cofibrations Carrier.{u, v} f) (Z : Carrier.{u, v}) :
    closedInclusions (f ▷ Z) := by
  intro a
  exact Spectra.NativeOmegaWeakClosure.nativeHEP_component_closed (f ▷ Z)
    (Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension.rightSmash_preserves_basedHEP
      f (Spectra.OriginalMonoidHEPClosure.nativeCofibrations_le_basedHEP f hf) Z) a

/-- The actual braid gives closedness for the original coefficient-first tensor map. -/
theorem leftTensorClosed (Z : Carrier.{u, v}) {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : cofibrations Carrier.{u, v} f) : closedInclusions (Z ◁ f) := by
  have h := rightTensorClosed f hf Z
  intro a
  let E := EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) a
  let q : Arrow.mk (f ▷ Z) ≅ Arrow.mk (Z ◁ f) :=
    Arrow.isoMk (β_ X Z) (β_ Y Z) (BraidedCategory.braiding_naturality_left f Z).symm
  let p := E.mapArrow.mapIso q
  let W : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  exact (W.arrow_mk_iso_iff p).mp (h a)

/-- Positive finite pushout products retain all original arrows and their order. -/
theorem iteratedPushoutProductCofibration :
    {n : ℕ} → (hn : 0 < n) → {X Y : Fin n → Carrier.{u, v}} →
    (f : ∀ i, X i ⟶ Y i) → (∀ i, cofibrations Carrier.{u, v} (f i)) →
    cofibrations Carrier.{u, v} (FiniteCube.iteratedPushoutProduct f).hom
  | 0, hn, _, _, _, _ => (Nat.not_lt_zero _ hn).elim
  | 1, _, _, _, _, hf => hf 0
  | n + 2, _, _, _, f, hf =>
      Spectra.NativeStableMonoidal.SymmetricSmash.cofibrations_pushoutProduct_cofibrations
        (FiniteCube.iteratedPushoutProduct (fun i : Fin (n + 1) => f i.castSucc)).hom
        (f (Fin.last (n + 1)))
        (iteratedPushoutProductCofibration (Nat.zero_lt_succ n)
          (fun i : Fin (n + 1) => f i.castSucc) (fun i => hf i.castSucc))
        (hf (Fin.last (n + 1)))

/-- Every actual coefficient-weighted positive finite pushout product evaluates to a closed inclusion. -/
theorem weightedPushoutProductClosed {n : ℕ} (hn : 0 < n)
    {X Y : Fin n → Carrier.{u, v}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, cofibrations Carrier.{u, v} (f i)) (Z : Carrier.{u, v}) :
    closedInclusions (Z ◁ (FiniteCube.iteratedPushoutProduct f).hom) :=
  leftTensorClosed Z _ (iteratedPushoutProductCofibration hn f hf)

/-- The actual coefficient-last orientation retains the same positive finite PP and coefficient. -/
theorem weightedRightPushoutProductClosed {n : ℕ} (hn : 0 < n)
    {X Y : Fin n → Carrier.{u, v}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, cofibrations Carrier.{u, v} (f i)) (Z : Carrier.{u, v}) :
    closedInclusions ((FiniteCube.iteratedPushoutProduct f).hom ▷ Z) :=
  rightTensorClosed _ (iteratedPushoutProductCofibration hn f hf) Z

end NativeCofibrations

section FiniteActions

variable {G : Type w} [Group G] [Finite G]

private theorem finiteActionPointedColimits :
    HasColimitsOfShape (SingleObj G) PointedCGWH.{u, v} := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Small.{v} G := small_of_injective (Fintype.equivFin G).injective
  let _ : LocallySmall.{v} (SingleObj G) :=
    { hom_small _ _ := inferInstanceAs (Small.{v} G) }
  let _ : EssentiallySmall.{v} (SingleObj G) :=
    essentiallySmall_of_small_of_locallySmall _
  exact HasColimitsOfShape.of_essentiallySmall.{v, v} PointedCGWH.{u, v} (SingleObj G)

attribute [local instance] finiteActionPointedColimits

/-- The whole original action is kept on its original single-object group diagram. -/
abbrev nativeActionDiagram (A : Action Carrier.{u, v} G) : SingleObj G ⥤ Carrier.{u, v} :=
  (Action.functorCategoryEquivalence Carrier.{u, v} G).functor.obj A

/-- Any supplied original action colimit square preserves evaluated closed inclusions. -/
theorem orbitCoconeMapClosed
    {A D : Action Carrier.{u, v} G} (p : A ⟶ D)
    (cA : Cocone (nativeActionDiagram A)) (cD : Cocone (nativeActionDiagram D))
    (hA : IsColimit cA) (hD : IsColimit cD) (m : cA.pt ⟶ cD.pt)
    (hm : ∀ j, cA.ι.app j ≫ m = p.hom ≫ cD.ι.app j)
    (hp : closedInclusions p.hom) : closedInclusions m := by
  intro a
  let E := evaluation (V := PointedCGWH.{u, v}) a
  let cAE : Cocone (PointedCGWH.actionDiagram ((E.mapAction G).obj A)) := E.mapCocone cA
  let cDE : Cocone (PointedCGWH.actionDiagram ((E.mapAction G).obj D)) := E.mapCocone cD
  let hAE : IsColimit cAE := isColimitOfPreserves E hA
  let hDE : IsColimit cDE := isColimitOfPreserves E hD
  exact PointedCGWH.isClosedEmbedding_orbitCoconeMap
    ((E.mapAction G).map p) cAE cDE hAE hDE (E.map m) (by
      intro j
      exact (E.map_comp _ _).symm.trans
        ((E.congr_map (hm j)).trans (E.map_comp _ _))) (hp a)

/-- The actual selected colimit map is the map of the same two original action cocones. -/
theorem orbitColimMapClosed
    {A D : Action Carrier.{u, v} G} (p : A ⟶ D)
    [HasColimit (nativeActionDiagram A)] [HasColimit (nativeActionDiagram D)]
    (hp : closedInclusions p.hom) :
    closedInclusions
      (colimMap ((Action.functorCategoryEquivalence Carrier.{u, v} G).functor.map p)) :=
  orbitCoconeMapClosed p (colimit.cocone (nativeActionDiagram A))
    (colimit.cocone (nativeActionDiagram D)) (colimit.isColimit _)
    (colimit.isColimit _) _ (fun j => ι_colimMap _ j) hp

end FiniteActions

section ProfileCells

open Operad OperadicOrbitCells OperadicOrbitCells.ProfileGeometry
open Operad.Tensor Operad.Tensor.InitialAttachment Operad.Tensor.InitialAttachment.ProfileCells
open Operad.Tensor.Enveloping Operad.Tensor.Enveloping.Filtration

attribute [local instance] FintypeCat.fintype

/-- The finite tensor is constructed from the actual native symmetric smash. -/
local instance nativeFiniteTensor : FiniteTensor Carrier.{u, v} := FiniteTensor.ofSymmetric _

private instance profileAutomorphismFinite {W : Type w} (P : ColoredProfile W) : Finite (Aut P) :=
  Finite.of_injective (fun g : Aut P => g.asIso.hom.inputEquiv) (by
    intro f g h
    apply Aut.ext
    apply Iso.ext
    exact ColoredProfile.Hom.ext h)

section NativeProfiles

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual coefficient-action orbit map evaluates closed before entering any filtration. -/
theorem coefficientOrbitClosed
    {G : Type w} [Group G] [Finite G] [HasColimitsOfShape (SingleObj G) Carrier.{u, v}]
    (Y : Action Carrier.{u, v} G) {A D : Action Carrier.{u, v} G} (p : A ⟶ D)
    (hp : cofibrations Carrier.{u, v} p.hom) :
    closedInclusions (coefficientOrbitArrow Y p).hom := by
  apply orbitColimMapClosed (Y ◁ p)
  exact leftTensorClosed Y.V p.hom hp

/-- Every original positive heterogeneous profile keeps its entire coefficient and PP action. -/
theorem profileIteratedOrbitClosed
    {W : Type w} {X Xprime : W → Carrier.{u, v}} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hP : 0 < inputCount P)
    (Y : Action Carrier.{u, v} (Aut P))
    (hx : ∀ i : P.inputs, cofibrations Carrier.{u, v} (x (P.inputColor i))) :
    closedInclusions (profileIteratedOrbitArrow x P Y).hom := by
  apply coefficientOrbitClosed Y (profilePushoutProductHom x P)
  exact iteratedPushoutProductCofibration hP (profileArrowFamily x P)
    (fun i => hx (inputEnumeration P i))

/-- The original balanced A5 profile arrow has closed evaluated inclusions in every operator value. -/
theorem balancedProfileClosed
    {W : Type w} (O : ColoredOperadObj W Carrier.{u, v})
    {X Xprime : W → Carrier.{u, v}} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hP : 0 < inputCount P)
    (hx : ∀ i : P.inputs, cofibrations Carrier.{u, v} (x (P.inputColor i))) :
    closedInclusions (balancedProfileArrow O x P).hom :=
  (closedInclusions.arrow_iso_iff
    (OperadicOrbitCells.A5Comparison.CanonicalOrbit.operadCoefficientOrbitIso O x P)).mpr
      (profileIteratedOrbitClosed x P hP
        (OperadicOrbitCells.A5Comparison.operadCoefficientAction O P) hx)

end NativeProfiles

/-- All original colors and operator values are kept when testing a carrier-family map. -/
def familyClosedInclusions (W : Type w) : MorphismProperty (W → Carrier.{u, v}) :=
  fun _ _ f => ∀ d : W, closedInclusions (f d)

instance familyClosedInclusions_respectsIso (W : Type w) :
    (familyClosedInclusions.{u, v} W).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    intro f g e hf d
    exact (closedInclusions.arrow_iso_iff
      ((Pi.eval (fun _ : W => Carrier.{u, v}) d).mapArrow.mapIso e)).mp (hf d))

instance familyClosedInclusions_isStableUnderCobaseChange (W : Type w) :
    (familyClosedInclusions.{u, v} W).IsStableUnderCobaseChange where
  of_isPushout sq hf d :=
    closedInclusions.of_isPushout
      (sq.map (Pi.eval (fun _ : W => Carrier.{u, v}) d)) (hf d)

instance familyClosedInclusions_isStableUnderRetracts (W : Type w) :
    (familyClosedInclusions.{u, v} W).IsStableUnderRetracts where
  of_retract h hg d :=
    closedInclusions.of_retract (h.map (Pi.eval (fun _ : W => Carrier.{u, v}) d)) (hg d)

instance familyClosedInclusions_isStableUnderCoproducts (W : Type w) :
    (familyClosedInclusions.{u, v} W).IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape J :=
    { condition := by
        intro F₁ F₂ c₁ c₂ hc₁ hc₂ p hp m hm d
        let E := Pi.eval (fun _ : W => Carrier.{u, v}) d
        exact MorphismProperty.IsStableUnderColimitsOfShape.condition
          (W := closedInclusions) (F₁ ⋙ E) (F₂ ⋙ E)
          (E.mapCocone c₁) (E.mapCocone c₂)
          (isColimitOfPreserves E hc₁) (isColimitOfPreserves E hc₂)
          (Functor.whiskerRight p E) (fun j => hp j d) (E.map m) (by
            intro j
            exact (E.map_comp _ _).symm.trans
              ((E.congr_map (hm j)).trans (E.map_comp _ _))) }

instance familyClosedInclusions_isStableUnderTransfiniteComposition (W : Type w) :
    (familyClosedInclusions.{u, v} W).IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape J :=
    { le := by
        rintro X Y f ⟨c⟩ d
        let E := Pi.eval (fun _ : W => Carrier.{u, v}) d
        let _ : PreservesWellOrderContinuousOfShape J E :=
          { preservesColimitsOfShape := fun _ _ => inferInstance }
        let ce : closedInclusions.TransfiniteCompositionOfShape J (E.map f) :=
          { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map E
            map_mem j hj := c.map_mem j hj d }
        exact closedInclusions.transfiniteCompositionsOfShape_le J _ ce.mem }

private instance familyClosedSmallTransfinite (W : Type w) :
    (familyClosedInclusions.{u, v} W).IsStableUnderTransfiniteComposition.{0} :=
  MorphismProperty.IsStableUnderTransfiniteComposition.shrink₀ _

/-- The actual supported cell has its original closed map at the output and isomorphisms elsewhere. -/
theorem colorMapClosed {W : Type w} (d : W) {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : closedInclusions f) : familyClosedInclusions W (colorMap d f) := by
  intro e
  by_cases he : e = d
  · subst e
    let q : Arrow.mk (colorMap d f d) ≅ Arrow.mk f :=
      Arrow.isoMk (atColorIso d X) (atColorIso d Y) (colorMap_at d f).symm
    exact (closedInclusions.arrow_mk_iso_iff q).mpr hf
  · have hi : IsIso (colorMap d f e) := by
      let a := awayColorIso d X e he
      let b := awayColorIso d Y e he
      have h : colorMap d f e = a.hom ≫ b.inv := dite_eq_right he
      rw [h]
      infer_instance
    exact closedInclusions.of_isIso _

variable {W : Type w} [Small.{v} W]

local instance nativeTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{_, _, v} Carrier.{u, v} :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot _

local instance nativeProfileColimits (d : W) :
    HasColimitsOfShape (AnalyticIndex W d) Carrier.{u, v} :=
  hasProfileColimitsOfSmallColors.{w, v} _ d

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Each genuine occurring cell uses its actual positive degree, Env coefficient and two Aut quotients. -/
theorem profileCellMapClosed (O : ColoredOperadObj W Carrier.{u, v}) (A : Algebra O)
    {X Xprime : W → Carrier.{u, v}} (x : X ⟶ Xprime)
    (hx : ∀ d : W, cofibrations Carrier.{u, v} (x d)) (N : ℕ) (p : RawCellIndex W N) :
    familyClosedInclusions W (profileCellMap O A x N p) := by
  apply colorMapClosed
  apply balancedProfileClosed (envelopingOperad.{w, _, _, v} O A) x (representativeProfile p.1 p.2)
  · rw [representativeProfile_degree]
    exact Nat.zero_lt_succ N
  · intro i
    exact hx _

/-- The original whole-family A5 relative complex itself has closed evaluated successor maps. -/
def originalEnvelopingClosedHistory (O : ColoredOperadObj W Carrier.{u, v}) (A : Algebra O)
    {X Xprime : W → Carrier.{u, v}} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A)
    (hx : ∀ d : W, cofibrations Carrier.{u, v} (x d)) :
    (familyClosedInclusions W).TransfiniteCompositionOfShape ℕ (OriginalAttachment.oldMap O A x y).hom := by
  let c := originalRelativeCellComplex.{w, _, _, v} O A x y
  let d := c.transfiniteCompositionOfShape'
    (I := familyClosedInclusions W) (fun s => profileCellMapClosed O A x hx s.j s.i)
  have hClosure : ((familyClosedInclusions W).coproducts.{v}).pushouts ≤ familyClosedInclusions W :=
    (MorphismProperty.pushouts_monotone (familyClosedInclusions W).coproducts_le).trans
      (familyClosedInclusions W).pushouts_le
  exact d.ofLE hClosure

/-- The actual original free-algebra pushout old leg is closed in every original color and level. -/
theorem originalEnvelopingOldMapClosed (O : ColoredOperadObj W Carrier.{u, v}) (A : Algebra O)
    {X Xprime : W → Carrier.{u, v}} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A)
    (hx : ∀ d : W, cofibrations Carrier.{u, v} (x d)) :
    familyClosedInclusions W (OriginalAttachment.oldMap O A x y).hom :=
  (familyClosedInclusions W).transfiniteCompositionsOfShape_le ℕ _
    (originalEnvelopingClosedHistory O A x y hx).mem

end ProfileCells

section TensorWords

open CategoryTheory.MonoidalCategory.MonoidWordPushout

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

local instance nativeWordPuncturedColimits (n : ℕ) :
    HasColimitsOfShape (FiniteCube.Punctured n) Carrier.{u, v} :=
  HasColimitsOfShape.of_essentiallySmall.{v, v} _ _

/-- The actual positive word attaching arrow is its original PP with all original old coefficients. -/
theorem wordAttachingMapClosed (A : Mon Carrier.{u, v}) {K L : Carrier.{u, v}}
    (f : K ⟶ L) (hf : cofibrations Carrier.{u, v} f) (n : ℕ) :
    closedInclusions (FiniteCube.boundaryToTop (wordCube A f (n + 1))) := by
  apply originalWordBoundaryTransport
    (HC := (inferInstance : HasColimitsOfSize.{v, v} Carrier.{u, v}))
    closedInclusions A (K := K) (L := L) f (n + 1)
  exact weightedRightPushoutProductClosed (n := n + 1)
    (X := fun _ : Fin (n + 1) => K) (Y := fun _ : Fin (n + 1) => L)
    (Nat.zero_lt_succ n) (fun _ => f) (fun _ => hf)
    (FiniteCube.coefficientObj (n := n + 1) (fun _ : Fin ((n + 1) + 1) => A.X))

/-- The complete original associative word history retains its actual endpoint and every stage map. -/
def originalWordClosedHistory (A : Mon Carrier.{u, v}) {K L : Carrier.{u, v}}
    (f : K ⟶ L) (a : TensorWord.tensorWordMon K ⟶ A) (hf : cofibrations Carrier.{u, v} f) :
    closedInclusions.TransfiniteCompositionOfShape ℕ (oldι A f a).hom where
  toTransfiniteCompositionOfShape := originalWordTransfiniteComposition.{_, _, v} A f a
  map_mem n _ := closedInclusions.of_isPushout
    (originalSuccessorIsPushout A (attachingValue A a) f n) (wordAttachingMapClosed A f hf n)

/-- The actual original associative free pushout old leg is closed at every original operator value. -/
theorem originalWordOldMapClosed (A : Mon Carrier.{u, v}) {K L : Carrier.{u, v}}
    (f : K ⟶ L) (a : TensorWord.tensorWordMon K ⟶ A) (hf : cofibrations Carrier.{u, v} f) :
    closedInclusions (oldι A f a).hom :=
  closedInclusions.transfiniteCompositionsOfShape_le ℕ _ (originalWordClosedHistory A f a hf).mem

end TensorWords

end PointedCGWH.NativeClosedCellHistory
