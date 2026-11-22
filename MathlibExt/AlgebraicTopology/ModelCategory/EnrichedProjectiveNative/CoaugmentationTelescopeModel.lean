/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescope
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderLevelSDR
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.ClosedStages
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.ClosedSequentialColimit.AtPoints
import MathlibExt.CategoryTheory.Filtered.NatTail
import MathlibExt.Topology.Category.CGWH.Colimits.ClosedWeakNatCocone
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHomotopyGroupInvariance

/-!
# Native coaugmentation telescope projections and homotopy colimits

The original mapping-cylinder deformation makes every stage projection
level weak for arbitrary sources. Its original second-endpoint maps are
closed at every native level. The same evaluated cocone therefore has
the actual compact homotopy-colimit comparisons, in every Type degree
and every positive Group degree.

Every point is represented in an actual stage beyond any requested
bound. Cofinal tails retain the physical telescope and the original
image point. Their Type and Group comparisons keep both maps and every
original leg. No source cofibrancy or telescope outcome is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra Topology
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.EnrichedCoaugmentationTelescope

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev Cat (J : Type) [EnrichedCategory PointedCGWH.{u, v} J] :=
  EnrichedFunctorCat PointedCGWH.{u, v} J

variable {F : (Cat.{u, v} I) ⥤ (Cat.{u, v} I)} (η : 𝟭 (Cat.{u, v} I) ⟶ F)

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.PointedAtGeometry.pointedNatColimits

/-- Every original projection is level weak by the actual arbitrary-source cylinder SDR. -/
theorem projection_weakEquivalence (n : ℕ) (X : Cat.{u, v} I) :
    WeakEquivalence ((projection η n).app X) := by
  cases n with
  | zero =>
    rw [projection_zero]
    change WeakEquivalence (𝟙 X)
    infer_instance
  | succ n =>
    rw [projection_succ_app]
    exact PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.retraction_weakEquivalence _

/-- The complete original projection weak class is retained in the native level model. -/
theorem projection_mem_weakEquivalences (n : ℕ) (X : Cat.{u, v} I) :
    weakEquivalences (Cat.{u, v} I) ((projection η n).app X) :=
  (HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence η n X)

/-- Every evaluated projection is the same actual native weak map. -/
theorem projection_component_weak (n : ℕ) (X : Cat.{u, v} I) (a : I) :
    weakEquivalences PointedCGWH.{u, v} (component ((projection η n).app X) a) := by
  have h := projection_mem_weakEquivalences η n X
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at h
  exact (EvaluationTransfer.evaluationProperty_iff
    (fun b : I => evaluation b) (weakEquivalences PointedCGWH.{u, v}) _).mp h a

omit B in
/-- The actual second-endpoint transition is closed at every native index. -/
theorem transition_component_isClosedEmbedding (n : ℕ) (X : Cat.{u, v} I) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component ((transition η n).app X) a).right) := by
  rw [transition_app]
  exact PointedCGWH.EnrichedIntervalMappingCylinderClosed.source_component_isClosedEmbedding _ a

omit B in
/-- Every full natural-number transition of the actual evaluated diagram is closed. -/
theorem evaluatedDiagram_map_isClosedEmbedding (X : Cat.{u, v} I) (a : I)
    {i j : ℕ} (f : i ⟶ j) :
    IsClosedEmbedding (ConcreteCategory.hom ((evaluatedDiagram η X a).map f).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  let D := evaluatedDiagram η X a
  have hStep (n : ℕ) : P (D.map (homOfLE (Nat.le_succ n))) := by
    change P ((evaluation a).map ((diagram η X).map (homOfLE (Nat.le_succ n))))
    rw [diagram_map_succ]
    exact transition_component_isClosedEmbedding η n X a
  have hMaps (j : ℕ) (hij : i ≤ j) : P (D.map (homOfLE hij)) := by
    induction j, hij using Nat.le_induction with
    | base => simpa only [homOfLE_refl, D.map_id] using P.id_mem (D.obj i)
    | succ j hij ih =>
      rw [← homOfLE_comp hij (Nat.le_succ j), D.map_comp]
      exact P.comp_mem _ _ ih (hStep j)
  change P (D.map f)
  rw [← homOfLE_leOfHom f]
  exact hMaps j (leOfHom f)

/-- The evaluated cocone keeps the actual physical telescope and every original leg. -/
def evaluatedCocone (X : Cat.{u, v} I) (a : I) : Cocone (evaluatedDiagram η X a) :=
  (evaluation a).mapCocone (colimit.cocone (diagram η X))

/-- Actual pointwise evaluation proves the universal property of that same cocone. -/
def evaluatedCoconeIsColimit (X : Cat.{u, v} I) (a : I) :
    IsColimit (evaluatedCocone η X a) :=
  isColimitOfPreserves (evaluation a) (colimit.isColimit (diagram η X))

omit B in
/-- Every evaluated cocone leg is the original full native stage leg component. -/
theorem evaluatedCocone_leg (X : Cat.{u, v} I) (a : I) (n : ℕ) :
    (evaluatedCocone η X a).ι.app n = component (leg η X n) a := rfl

omit B in
/-- All original native input arrows commute with the actual evaluated cocone legs. -/
theorem evaluatedCocone_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (n : ℕ) :
    (evaluatedCocone η X a).ι.app n ≫ component ((telescopeFunctor η).map f) a =
      (Functor.whiskerRight (diagramMap η f) (evaluation a)).app n ≫
        (evaluatedCocone η Y a).ι.app n :=
  ((evaluation a).map_comp _ _).symm.trans
    (((evaluation a).congr_map (leg_naturality η f n)).trans ((evaluation a).map_comp _ _))

omit B in
/-- Every original telescope point occurs at an actual stage after every prescribed bound. -/
theorem exists_stage_point_after (X : Cat.{u, v} I) (a : I)
    (x : ((telescope η X).toEnrichedFunctor.obj a).right) (n₀ : ℕ) :
    ∃ (n : ℕ), n₀ ≤ n ∧
      ∃ (p : (((stage η n).functor.obj X).toEnrichedFunctor.obj a).right),
        (component (leg η X n) a).right p = x := by
  obtain ⟨n, hn, g, hg⟩ := PointedCGWH.ClosedSequentialColimit.exists_later_stage_of_compact
    (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)
    (fun _ _ f => evaluatedDiagram_map_isClosedEmbedding η X a f)
    (K := PUnit.{1}) isCompact_univ (ContinuousMap.const PUnit.{1} x) n₀
  exact ⟨n, hn, g PUnit.unit, congrArg (fun f => f PUnit.unit) hg⟩

/-- The all-degree comparison uses the actual chosen Type colimit and original telescope. -/
def typeHomotopyIso (X : Cat.{u, v} I) (a : I) (k : ℕ) :
    colimit (evaluatedDiagram η X a ⋙ piNFunctor k) ≅
      piN k ((telescope η X).toEnrichedFunctor.obj a) :=
  PointedCGWH.SequentialHomotopyColimit.piNComparisonIso k
    (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)
    (fun _ _ f => evaluatedDiagram_map_isClosedEmbedding η X a f)

/-- Positive groups use the genuine original filtered Group colimit, including degree one. -/
def positiveHomotopyIso (X : Cat.{u, v} I) (a : I) (k : ℕ) :
    GrpCat.FilteredColimits.colimit (evaluatedDiagram η X a ⋙ piNPositiveFunctor k) ≅
      (piNPositiveFunctor k).obj ((telescope η X).toEnrichedFunctor.obj a) :=
  PointedCGWH.SequentialHomotopyColimit.piNPositiveComparisonIso k
    (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)
    (fun _ _ f => evaluatedDiagram_map_isClosedEmbedding η X a f)

omit B in
/-- Every forward Type comparison leg is the original stage-leg homotopy map. -/
theorem typeHomotopyIso_hom_leg (X : Cat.{u, v} I) (a : I) (k n : ℕ) :
    colimit.ι (evaluatedDiagram η X a ⋙ piNFunctor k) n ≫ (typeHomotopyIso η X a k).hom =
      (piNFunctor k).map (component (leg η X n) a) :=
  PointedCGWH.SequentialHomotopyColimit.piNComparisonIso_hom_ι k
    (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)
    (fun _ _ f => evaluatedDiagram_map_isClosedEmbedding η X a f) n

omit B in
/-- Every inverse Type comparison retains the same actual stage-leg map. -/
theorem typeHomotopyIso_inv_leg (X : Cat.{u, v} I) (a : I) (k n : ℕ) :
    (piNFunctor k).map (component (leg η X n) a) ≫ (typeHomotopyIso η X a k).inv =
      colimit.ι (evaluatedDiagram η X a ⋙ piNFunctor k) n :=
  PointedCGWH.SequentialHomotopyColimit.piNComparisonIso_inv_ι k
    (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)
    (fun _ _ f => evaluatedDiagram_map_isClosedEmbedding η X a f) n

omit B in
/-- Every forward positive comparison retains the original Group stage leg. -/
theorem positiveHomotopyIso_hom_leg (X : Cat.{u, v} I) (a : I) (k n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone
      (evaluatedDiagram η X a ⋙ piNPositiveFunctor k)).ι.app n ≫
        (positiveHomotopyIso η X a k).hom =
      (piNPositiveFunctor k).map (component (leg η X n) a) := by
  rw [show (positiveHomotopyIso η X a k).hom =
      PointedCGWH.SequentialHomotopyColimit.piNPositiveComparison k (evaluatedCocone η X a)
    from PointedCGWH.SequentialHomotopyColimit.piNPositiveComparisonIso_hom k
      (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)
      (fun _ _ f => evaluatedDiagram_map_isClosedEmbedding η X a f)]
  exact PointedCGWH.SequentialHomotopyColimit.piNPositiveComparison_ι k
    (evaluatedCocone η X a) n

omit B in
/-- Every inverse positive comparison retains the same actual Group stage leg. -/
theorem positiveHomotopyIso_inv_leg (X : Cat.{u, v} I) (a : I) (k n : ℕ) :
    (piNPositiveFunctor k).map (component (leg η X n) a) ≫
        (positiveHomotopyIso η X a k).inv =
      (GrpCat.FilteredColimits.colimitCocone
        (evaluatedDiagram η X a ⋙ piNPositiveFunctor k)).ι.app n :=
  PointedCGWH.SequentialHomotopyColimit.piNPositiveComparisonIso_inv_ι k
    (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)
    (fun _ _ f => evaluatedDiagram_map_isClosedEmbedding η X a f) n

omit B in
/-- The complete Type comparison is natural on every original native input arrow. -/
theorem typeHomotopyIso_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (k : ℕ) :
    colim.map (Functor.whiskerRight (Functor.whiskerRight (diagramMap η f) (evaluation a))
        (piNFunctor k)) ≫ (typeHomotopyIso η Y a k).hom =
      (typeHomotopyIso η X a k).hom ≫
        (piNFunctor k).map (component ((telescopeFunctor η).map f) a) :=
  PointedCGWH.SequentialHomotopyColimit.piNComparisonIso_naturality k
    (evaluatedCocone η X a) (evaluatedCocone η Y a)
    (evaluatedCoconeIsColimit η X a) (evaluatedCoconeIsColimit η Y a)
    (fun _ _ g => evaluatedDiagram_map_isClosedEmbedding η X a g)
    (fun _ _ g => evaluatedDiagram_map_isClosedEmbedding η Y a g)
    (Functor.whiskerRight (diagramMap η f) (evaluation a))
    (component ((telescopeFunctor η).map f) a) (evaluatedCocone_naturality η f a)

omit B in
/-- The complete positive Group comparison is natural on every original native input arrow. -/
theorem positiveHomotopyIso_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (k : ℕ) :
    GrpCat.FilteredColimits.colimitMap
      (Functor.whiskerRight (Functor.whiskerRight (diagramMap η f) (evaluation a))
        (piNPositiveFunctor k)) ≫ (positiveHomotopyIso η Y a k).hom =
      (positiveHomotopyIso η X a k).hom ≫
        (piNPositiveFunctor k).map (component ((telescopeFunctor η).map f) a) :=
  PointedCGWH.SequentialHomotopyColimit.piNPositiveComparisonIso_naturality k
    (evaluatedCocone η X a) (evaluatedCocone η Y a)
    (evaluatedCoconeIsColimit η X a) (evaluatedCoconeIsColimit η Y a)
    (fun _ _ g => evaluatedDiagram_map_isClosedEmbedding η X a g)
    (fun _ _ g => evaluatedDiagram_map_isClosedEmbedding η Y a g)
    (Functor.whiskerRight (diagramMap η f) (evaluation a))
    (component ((telescopeFunctor η).map f) a) (evaluatedCocone_naturality η f a)

omit B in
/-- The inverse Type comparison is natural on the same complete native input map. -/
theorem typeHomotopyIso_inv_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (k : ℕ) :
    (piNFunctor k).map (component ((telescopeFunctor η).map f) a) ≫
        (typeHomotopyIso η Y a k).inv =
      (typeHomotopyIso η X a k).inv ≫
        colim.map (Functor.whiskerRight
          (Functor.whiskerRight (diagramMap η f) (evaluation a)) (piNFunctor k)) :=
  (CommSq.vert_inv (g := typeHomotopyIso η X a k)
    (h := typeHomotopyIso η Y a k) ⟨typeHomotopyIso_naturality η f a k⟩).w

omit B in
/-- The inverse positive Group comparison keeps the same original native input map. -/
theorem positiveHomotopyIso_inv_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (k : ℕ) :
    (piNPositiveFunctor k).map (component ((telescopeFunctor η).map f) a) ≫
        (positiveHomotopyIso η Y a k).inv =
      (positiveHomotopyIso η X a k).inv ≫
        GrpCat.FilteredColimits.colimitMap (Functor.whiskerRight
          (Functor.whiskerRight (diagramMap η f) (evaluation a)) (piNPositiveFunctor k)) :=
  (CommSq.vert_inv (g := positiveHomotopyIso η X a k)
    (h := positiveHomotopyIso η Y a k) ⟨positiveHomotopyIso_naturality η f a k⟩).w

/-- The underlying evaluated tail retains the physical telescope and shifted original legs. -/
def underlyingTailCocone (X : Cat.{u, v} I) (a : I) (r : ℕ) :
    Cocone (CategoryTheory.NatTail.tailFunctor r ⋙
      (evaluatedDiagram η X a ⋙ pointedToCGWH)) :=
  (pointedToCGWH.mapCocone (evaluatedCocone η X a)).whisker
    (CategoryTheory.NatTail.tailFunctor r)

/-- The same original evaluated cocone has its actual underlying CGWH universal property. -/
def underlyingEvaluatedIsColimit (X : Cat.{u, v} I) (a : I) :
    IsColimit (pointedToCGWH.mapCocone (evaluatedCocone η X a)) :=
  PointedCGWH.ClosedSequentialColimit.isColimitCGWH
    (evaluatedCocone η X a) (evaluatedCoconeIsColimit η X a)

/-- Genuine finality proves the universal property of every actual original tail. -/
def underlyingTailIsColimit (X : Cat.{u, v} I) (a : I) (r : ℕ) :
    IsColimit (underlyingTailCocone η X a r) := by
  let _ : (CategoryTheory.NatTail.tailFunctor r).Final :=
    CategoryTheory.NatTail.tailFunctor_final r
  exact (Functor.Final.isColimitWhiskerEquiv (CategoryTheory.NatTail.tailFunctor r)
    (pointedToCGWH.mapCocone (evaluatedCocone η X a))).symm
      (underlyingEvaluatedIsColimit η X a)

omit B in
/-- The entire tail has the same literal physical telescope point. -/
theorem underlyingTailCocone_pt (X : Cat.{u, v} I) (a : I) (r : ℕ) :
    (underlyingTailCocone η X a r).pt = ((telescope η X).toEnrichedFunctor.obj a).right :=
  rfl

omit B in
/-- Every underlying tail leg is exactly the original shifted native stage leg. -/
theorem underlyingTailCocone_leg (X : Cat.{u, v} I) (a : I) (r n : ℕ) :
    (underlyingTailCocone η X a r).ι.app n = (component (leg η X (r + n)) a).right :=
  rfl

omit B in
/-- Every underlying tail transition is the same actual closed stage map. -/
theorem underlyingTail_map_isClosedEmbedding (X : Cat.{u, v} I) (a : I) (r : ℕ)
    {i j : ℕ} (f : i ⟶ j) :
    IsClosedEmbedding (ConcreteCategory.hom
      ((CategoryTheory.NatTail.tailFunctor r ⋙
        (evaluatedDiagram η X a ⋙ pointedToCGWH)).map f)) :=
  evaluatedDiagram_map_isClosedEmbedding η X a ((CategoryTheory.NatTail.tailFunctor r).map f)

/-- Every stage point is followed through the full original based tail. -/
def basedTailDiagram (X : Cat.{u, v} I) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    ℕ ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.PointedAtGeometry.diagramAt
    (CategoryTheory.NatTail.tailFunctor r ⋙ (evaluatedDiagram η X a ⋙ pointedToCGWH)) p

/-- The based tail cocone retains that same physical telescope at its actual image point. -/
def basedTailCocone (X : Cat.{u, v} I) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    Cocone (basedTailDiagram η X a r p) :=
  PointedCGWH.PointedAtGeometry.coconeAt (underlyingTailCocone η X a r) p

/-- Its colimit proof comes from the original whole tail, without changing its point. -/
def basedTailIsColimit (X : Cat.{u, v} I) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    IsColimit (basedTailCocone η X a r p) :=
  PointedCGWH.PointedAtGeometry.coconeAtIsColimit
    (underlyingTailCocone η X a r) (underlyingTailIsColimit η X a r) p

omit B in
/-- The whole based tail retains the original telescope and original stage-image point. -/
theorem basedTailCocone_pt (X : Cat.{u, v} I) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailCocone η X a r p).pt =
      PointedCGWH.pointedAt ((telescope η X).toEnrichedFunctor.obj a).right
        ((component (leg η X r) a).right p) := rfl

/-- Every Type degree has both actual comparison functions at every original stage point. -/
def basedTailTypeIso (X : Cat.{u, v} I) (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    colimit (basedTailDiagram η X a r p ⋙ piNFunctor k) ≅
      (piNFunctor k).obj (basedTailCocone η X a r p).pt :=
  PointedCGWH.SequentialHomotopyColimit.piNComparisonIso k
    (basedTailCocone η X a r p) (basedTailIsColimit η X a r p)
    (fun _ _ f => underlyingTail_map_isClosedEmbedding η X a r f)

/-- Every positive Group degree has both actual filtered comparison maps at each stage point. -/
def basedTailPositiveIso (X : Cat.{u, v} I) (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    GrpCat.FilteredColimits.colimit (basedTailDiagram η X a r p ⋙ piNPositiveFunctor k) ≅
      (piNPositiveFunctor k).obj (basedTailCocone η X a r p).pt :=
  PointedCGWH.SequentialHomotopyColimit.piNPositiveComparisonIso k
    (basedTailCocone η X a r p) (basedTailIsColimit η X a r p)
    (fun _ _ f => underlyingTail_map_isClosedEmbedding η X a r f)

omit B in
/-- Every based forward Type leg is the original based stage-leg map. -/
theorem basedTailTypeIso_hom_leg (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    colimit.ι (basedTailDiagram η X a r p ⋙ piNFunctor k) n ≫
        (basedTailTypeIso η X a r k p).hom =
      (piNFunctor k).map ((basedTailCocone η X a r p).ι.app n) :=
  PointedCGWH.SequentialHomotopyColimit.piNComparisonIso_hom_ι k
    (basedTailCocone η X a r p) (basedTailIsColimit η X a r p)
    (fun _ _ f => underlyingTail_map_isClosedEmbedding η X a r f) n

omit B in
/-- Every based inverse Type leg keeps the same original based map. -/
theorem basedTailTypeIso_inv_leg (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (piNFunctor k).map ((basedTailCocone η X a r p).ι.app n) ≫
        (basedTailTypeIso η X a r k p).inv =
      colimit.ι (basedTailDiagram η X a r p ⋙ piNFunctor k) n :=
  PointedCGWH.SequentialHomotopyColimit.piNComparisonIso_inv_ι k
    (basedTailCocone η X a r p) (basedTailIsColimit η X a r p)
    (fun _ _ f => underlyingTail_map_isClosedEmbedding η X a r f) n

omit B in
/-- Every based forward Group leg is the same actual positive-degree stage map. -/
theorem basedTailPositiveIso_hom_leg (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (GrpCat.FilteredColimits.colimitCocone
      (basedTailDiagram η X a r p ⋙ piNPositiveFunctor k)).ι.app n ≫
        (basedTailPositiveIso η X a r k p).hom =
      (piNPositiveFunctor k).map ((basedTailCocone η X a r p).ι.app n) :=
  PointedCGWH.SequentialHomotopyColimit.piNPositiveComparison_ι k
    (basedTailCocone η X a r p) n

omit B in
/-- Every based inverse Group leg retains the original genuine filtered quotient. -/
theorem basedTailPositiveIso_inv_leg (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (piNPositiveFunctor k).map ((basedTailCocone η X a r p).ι.app n) ≫
        (basedTailPositiveIso η X a r k p).inv =
      (GrpCat.FilteredColimits.colimitCocone
        (basedTailDiagram η X a r p ⋙ piNPositiveFunctor k)).ι.app n :=
  PointedCGWH.SequentialHomotopyColimit.piNPositiveComparisonIso_inv_ι k
    (basedTailCocone η X a r p) (basedTailIsColimit η X a r p)
    (fun _ _ f => underlyingTail_map_isClosedEmbedding η X a r f) n

/-- The whole underlying tail map consists of the original shifted native stage maps. -/
def underlyingTailMap {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (r : ℕ) :
    CategoryTheory.NatTail.tailFunctor r ⋙ (evaluatedDiagram η X a ⋙ pointedToCGWH) ⟶
      CategoryTheory.NatTail.tailFunctor r ⋙ (evaluatedDiagram η Y a ⋙ pointedToCGWH) :=
  Functor.whiskerLeft (CategoryTheory.NatTail.tailFunctor r)
    (Functor.whiskerRight (Functor.whiskerRight (diagramMap η f) (evaluation a)) pointedToCGWH)

omit B in
/-- Its every component is the original native input map at that actual shifted stage. -/
theorem underlyingTailMap_app {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (r n : ℕ) :
    (underlyingTailMap η f a r).app n =
      (component ((stage η (r + n)).functor.map f) a).right := rfl

omit B in
/-- The actual telescope map commutes with every original underlying tail leg. -/
theorem underlyingTailCocone_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (r n : ℕ) :
    (underlyingTailCocone η X a r).ι.app n ≫
        (component ((telescopeFunctor η).map f) a).right =
      (underlyingTailMap η f a r).app n ≫ (underlyingTailCocone η Y a r).ι.app n :=
  (pointedToCGWH.map_comp _ _).symm.trans
    ((pointedToCGWH.congr_map (evaluatedCocone_naturality η f a (r + n))).trans
      (pointedToCGWH.map_comp _ _))

/-- The given actual stage point is carried by the whole original native stage input map. -/
def basedTailMap {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    basedTailDiagram η X a r p ⟶ basedTailDiagram η Y a r
      ((component ((stage η r).functor.map f) a).right p) :=
  PointedCGWH.PointedAtGeometry.diagramAtMap (underlyingTailMap η f a r) p

omit B in
/-- Repointing preserves every actual shifted native input map. -/
theorem basedTailMap_right {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (r n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    ((basedTailMap η f a r p).app n).right =
      (component ((stage η (r + n)).functor.map f) a).right := rfl

/-- The based telescope map retains the actual original map and its actual image point. -/
def basedTailCoconeMap {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailCocone η X a r p).pt ⟶ (basedTailCocone η Y a r
      ((component ((stage η r).functor.map f) a).right p)).pt :=
  PointedCGWH.PointedAtGeometry.coconeAtMap
    (underlyingTailCocone η X a r) (underlyingTailCocone η Y a r)
    (underlyingTailMap η f a r) (component ((telescopeFunctor η).map f) a).right
    (underlyingTailCocone_naturality η f a r) p

omit B in
/-- Its right map is the original entire native telescope input map. -/
theorem basedTailCoconeMap_right {X Y : Cat.{u, v} I} (f : X ⟶ Y) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailCoconeMap η f a r p).right =
      (component ((telescopeFunctor η).map f) a).right := rfl

omit B in
/-- At every original stage point, the original telescope input map after the stage leg equals
the original stage input map followed by its target stage leg. This keeps the whole original
pointwise equation obtained from the actual evaluated cocone naturality. -/
theorem basedTail_image_point_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (r : ℕ) :
    (fun {P : Prop} (_ : P) => P)
      (ConcreteCategory.congr_hom
        (pointedToCGWH.congr_map (evaluatedCocone_naturality η f a r))) :=
  ConcreteCategory.congr_hom
    (pointedToCGWH.congr_map (evaluatedCocone_naturality η f a r))

@[deprecated basedTail_image_point_naturality (since := "2026-10-31")]
alias basedTailImagePointNaturality := basedTail_image_point_naturality

omit B in
/-- Both actual based maps commute with every original based tail leg. -/
theorem basedTailCoconeMap_leg {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (r n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailCocone η X a r p).ι.app n ≫ basedTailCoconeMap η f a r p =
      (basedTailMap η f a r p).app n ≫ (basedTailCocone η Y a r
        ((component ((stage η r).functor.map f) a).right p)).ι.app n :=
  PointedCGWH.PointedAtGeometry.coconeAtMap_leg
    (underlyingTailCocone η X a r) (underlyingTailCocone η Y a r)
    (underlyingTailMap η f a r) (component ((telescopeFunctor η).map f) a).right
    (underlyingTailCocone_naturality η f a r) p n

omit B in
/-- The forward Type comparison commutes with every complete native input map and stage point. -/
theorem basedTailTypeIso_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    colim.map (Functor.whiskerRight (basedTailMap η f a r p) (piNFunctor k)) ≫
        (basedTailTypeIso η Y a r k
          ((component ((stage η r).functor.map f) a).right p)).hom =
      (basedTailTypeIso η X a r k p).hom ≫ (piNFunctor k).map (basedTailCoconeMap η f a r p) :=
  PointedCGWH.BasedClosedPiColimitGeometry.basedTypeComparisonIso_hom_naturality k
    (underlyingTailCocone η X a r) (underlyingTailCocone η Y a r)
    (underlyingTailIsColimit η X a r) (underlyingTailIsColimit η Y a r)
    (fun _ _ g => underlyingTail_map_isClosedEmbedding η X a r g)
    (fun _ _ g => underlyingTail_map_isClosedEmbedding η Y a r g)
    (underlyingTailMap η f a r) (component ((telescopeFunctor η).map f) a).right
    (underlyingTailCocone_naturality η f a r) p

omit B in
/-- The inverse Type comparison is natural for the same original native map and point. -/
theorem basedTailTypeIso_inv_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (piNFunctor k).map (basedTailCoconeMap η f a r p) ≫
        (basedTailTypeIso η Y a r k
          ((component ((stage η r).functor.map f) a).right p)).inv =
      (basedTailTypeIso η X a r k p).inv ≫
        colim.map (Functor.whiskerRight (basedTailMap η f a r p) (piNFunctor k)) :=
  (CommSq.vert_inv (g := basedTailTypeIso η X a r k p)
    (h := basedTailTypeIso η Y a r k
      ((component ((stage η r).functor.map f) a).right p))
    ⟨basedTailTypeIso_naturality η f a r k p⟩).w

omit B in
/-- The forward Group comparison retains the same native maps in every positive degree. -/
theorem basedTailPositiveIso_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    GrpCat.FilteredColimits.colimitMap
      (Functor.whiskerRight (basedTailMap η f a r p) (piNPositiveFunctor k)) ≫
        (basedTailPositiveIso η Y a r k
          ((component ((stage η r).functor.map f) a).right p)).hom =
      (basedTailPositiveIso η X a r k p).hom ≫
        (piNPositiveFunctor k).map (basedTailCoconeMap η f a r p) :=
  PointedCGWH.BasedClosedPiColimitGeometry.basedPositiveComparisonIso_hom_naturality k
    (underlyingTailCocone η X a r) (underlyingTailCocone η Y a r)
    (underlyingTailIsColimit η X a r) (underlyingTailIsColimit η Y a r)
    (fun _ _ g => underlyingTail_map_isClosedEmbedding η X a r g)
    (fun _ _ g => underlyingTail_map_isClosedEmbedding η Y a r g)
    (underlyingTailMap η f a r) (component ((telescopeFunctor η).map f) a).right
    (underlyingTailCocone_naturality η f a r) p

omit B in
/-- The inverse Group comparison is natural on the same original native map and stage point. -/
theorem basedTailPositiveIso_inv_naturality {X Y : Cat.{u, v} I} (f : X ⟶ Y)
    (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (piNPositiveFunctor k).map (basedTailCoconeMap η f a r p) ≫
        (basedTailPositiveIso η Y a r k
          ((component ((stage η r).functor.map f) a).right p)).inv =
      (basedTailPositiveIso η X a r k p).inv ≫
        GrpCat.FilteredColimits.colimitMap
          (Functor.whiskerRight (basedTailMap η f a r p) (piNPositiveFunctor k)) :=
  (CommSq.vert_inv (g := basedTailPositiveIso η X a r k p)
    (h := basedTailPositiveIso η Y a r k
      ((component ((stage η r).functor.map f) a).right p))
    ⟨basedTailPositiveIso_naturality η f a r k p⟩).w

/-- The native weak class is the original weak class at every actual underlying level. -/
theorem weakEquivalences_iff_components {X Y : Cat.{u, v} I} (f : X ⟶ Y) :
    weakEquivalences (Cat.{u, v} I) f ↔
      ∀ a : I, CGWH.weakHomotopyEquivalences (component f a).right := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq,
    EvaluationTransfer.evaluationProperty_iff]
  have hp {A C : PointedCGWH.{u, v}} (g : A ⟶ C) :
      weakEquivalences PointedCGWH.{u, v} g ↔ CGWH.weakHomotopyEquivalences g.right :=
    (HomotopicalAlgebra.weakEquivalence_iff g).symm.trans
      ((PointedCGWH.weakEquivalence_iff g).trans (CGWH.modelCategory.weakEquivalence_iff g.right))
  exact forall_congr' (fun a => hp (component f a))

/-- A stage preserves weakness whenever its actual original iterate preserves that input map. -/
theorem stage_map_mem_weak {X Y : Cat.{u, v} I} (f : X ⟶ Y) (n : ℕ)
    (hf : weakEquivalences (Cat.{u, v} I) ((Functor.Iteration.iterate F n).map f)) :
    weakEquivalences (Cat.{u, v} I) ((stage η n).functor.map f) := by
  let W := weakEquivalences (Cat.{u, v} I)
  have hpX : W ((projection η n).app X) := projection_mem_weakEquivalences η n X
  have hpY : W ((projection η n).app Y) := projection_mem_weakEquivalences η n Y
  have hn : W ((stage η n).functor.map f ≫ (projection η n).app Y) := by
    rw [(projection η n).naturality f]
    exact W.comp_mem _ _ hpX hf
  exact W.of_postcomp _ _ hpY hn

/-- An actual weak original-input transition makes its original cylinder transition weak. -/
theorem transition_mem_weak (n : ℕ) (X : Cat.{u, v} I)
    (hη : weakEquivalences (Cat.{u, v} I)
      ((Functor.Iteration.inputTransition η n).app X)) :
    weakEquivalences (Cat.{u, v} I) ((transition η n).app X) := by
  let W := weakEquivalences (Cat.{u, v} I)
  have hp : W ((projection η n).app X) := projection_mem_weakEquivalences η n X
  have hp' : W ((projection η (n + 1)).app X) := projection_mem_weakEquivalences η (n + 1) X
  have hn : W ((transition η n).app X ≫ (projection η (n + 1)).app X) := by
    rw [transition_projection_app]
    exact W.comp_mem _ _ hp hη
  exact W.of_postcomp _ _ hp' hn

/-- Every full diagram arrow is weak when the original-input transitions are weak. -/
theorem diagram_map_mem_weak (X : Cat.{u, v} I)
    (hη : ∀ n : ℕ, weakEquivalences (Cat.{u, v} I)
      ((Functor.Iteration.inputTransition η n).app X)) {i j : ℕ} (f : i ⟶ j) :
    weakEquivalences (Cat.{u, v} I) ((diagram η X).map f) := by
  let W := weakEquivalences (Cat.{u, v} I)
  let D := diagram η X
  have hStep (n : ℕ) : W (D.map (homOfLE (Nat.le_succ n))) := by
    rw [show D = diagram η X from rfl, diagram_map_succ]
    exact transition_mem_weak η n X (hη n)
  have hMaps (j : ℕ) (hij : i ≤ j) : W (D.map (homOfLE hij)) := by
    induction j, hij using Nat.le_induction with
    | base => simpa only [homOfLE_refl, D.map_id] using W.id_mem (D.obj i)
    | succ j hij ih =>
      rw [← homOfLE_comp hij (Nat.le_succ j), D.map_comp]
      exact W.comp_mem _ _ ih (hStep j)
  rw [← homOfLE_leOfHom f]
  exact hMaps j (leOfHom f)

/-- The actual original unit is weak at every level by genuine closed weak cocone closure. -/
theorem unit_component_mem_weak (X : Cat.{u, v} I)
    (hη : ∀ n : ℕ, weakEquivalences (Cat.{u, v} I)
      ((Functor.Iteration.inputTransition η n).app X)) (a : I) :
    CGWH.weakHomotopyEquivalences (component ((unit η).app X) a).right := by
  let D := evaluatedDiagram η X a ⋙ pointedToCGWH
  let c := pointedToCGWH.mapCocone (evaluatedCocone η X a)
  have hStep (n : ℕ) : CGWH.weakHomotopyEquivalences
      (D.map (homOfLE (Nat.le_succ n))) ∧
        IsClosedEmbedding (ConcreteCategory.hom (D.map (homOfLE (Nat.le_succ n)))) := by
    have hw := (weakEquivalences_iff_components ((transition η n).app X)).mp
      (transition_mem_weak η n X (hη n)) a
    have hc := transition_component_isClosedEmbedding η n X a
    change CGWH.weakHomotopyEquivalences
      ((evaluation a).map ((diagram η X).map (homOfLE (Nat.le_succ n)))).right ∧
        IsClosedEmbedding (ConcreteCategory.hom
          ((evaluation a).map ((diagram η X).map (homOfLE (Nat.le_succ n)))).right)
    rw [diagram_map_succ]
    exact ⟨hw, hc⟩
  exact CGWH.ClosedWeakNatCocone.endpoint_weak c (underlyingEvaluatedIsColimit η X a) hStep

/-- The original whole unit is weak when its actual original-input transitions are weak. -/
theorem unit_mem_weak (X : Cat.{u, v} I)
    (hη : ∀ n : ℕ, weakEquivalences (Cat.{u, v} I)
      ((Functor.Iteration.inputTransition η n).app X)) :
    weakEquivalences (Cat.{u, v} I) ((unit η).app X) :=
  (weakEquivalences_iff_components _).mpr (unit_component_mem_weak η X hη)

/-- Preservation by the given original functor iterates its given original weak input map. -/
theorem iterate_map_mem_weak
    (hF : ∀ {A C : Cat.{u, v} I} (f : A ⟶ C),
      weakEquivalences (Cat.{u, v} I) f → weakEquivalences (Cat.{u, v} I) (F.map f))
    {X Y : Cat.{u, v} I} (f : X ⟶ Y) (hf : weakEquivalences (Cat.{u, v} I) f) (n : ℕ) :
    weakEquivalences (Cat.{u, v} I) ((Functor.Iteration.iterate F n).map f) := by
  induction n with
  | zero => exact hf
  | succ n hn => exact hF _ hn

/-- The weak original coaugmentation is iterated on its original input, with no `η(FⁿX)` premise. -/
theorem inputTransition_mem_weak
    (hF : ∀ {A C : Cat.{u, v} I} (f : A ⟶ C),
      weakEquivalences (Cat.{u, v} I) f → weakEquivalences (Cat.{u, v} I) (F.map f))
    (X : Cat.{u, v} I) (hη : weakEquivalences (Cat.{u, v} I) (η.app X)) (n : ℕ) :
    weakEquivalences (Cat.{u, v} I) ((Functor.Iteration.inputTransition η n).app X) := by
  let W := weakEquivalences (Cat.{u, v} I)
  change W ((Functor.Iteration.iterate F n).map (η.app X) ≫
    (Functor.Iteration.iteratePrefixIso F n).inv.app X)
  exact W.comp_mem _ _ (iterate_map_mem_weak hF _ hη n) (W.of_isIso _)

/-- The actual telescope unit is weak from preservation and the original weak coaugmentation. -/
theorem unit_mem_weak_of_preserves
    (hF : ∀ {A C : Cat.{u, v} I} (f : A ⟶ C),
      weakEquivalences (Cat.{u, v} I) f → weakEquivalences (Cat.{u, v} I) (F.map f))
    (X : Cat.{u, v} I) (hη : weakEquivalences (Cat.{u, v} I) (η.app X)) :
    weakEquivalences (Cat.{u, v} I) ((unit η).app X) :=
  unit_mem_weak η X (inputTransition_mem_weak η hF X hη)

/-- The original-input tail retains every actual `Fⁿ(η_X)` map after the given stage. -/
def iterationTailUnderlying (X : Cat.{u, v} I) (a : I) (r : ℕ) : ℕ ⥤ CGWH.{u, v} :=
  CategoryTheory.NatTail.tailFunctor r ⋙
    ((Functor.Iteration.inputDiagram η X ⋙ evaluation a) ⋙ pointedToCGWH)

/-- The complete original projections compare the actual cylinder tail with that same input tail. -/
def projectionTailUnderlying (X : Cat.{u, v} I) (a : I) (r : ℕ) :
    CategoryTheory.NatTail.tailFunctor r ⋙ (evaluatedDiagram η X a ⋙ pointedToCGWH) ⟶
      iterationTailUnderlying η X a r :=
  Functor.whiskerLeft (CategoryTheory.NatTail.tailFunctor r)
    (Functor.whiskerRight (Functor.whiskerRight (diagramProjection η X) (evaluation a))
      pointedToCGWH)

omit B in
/-- Every original projected tail component is the same actual shifted native projection. -/
theorem projectionTailUnderlying_app (X : Cat.{u, v} I) (a : I) (r n : ℕ) :
    (projectionTailUnderlying η X a r).app n =
      (component ((projection η (r + n)).app X) a).right := rfl

/-- The raw input tail is based at the actual image of the given original cylinder-stage point. -/
def iterationTailBasedDiagram (X : Cat.{u, v} I) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    ℕ ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.PointedAtGeometry.diagramAt (iterationTailUnderlying η X a r)
    ((projectionTailUnderlying η X a r).app 0 p)

/-- Repointing the original whole tail projection retains its complete original diagram map. -/
def basedTailProjection (X : Cat.{u, v} I) (a : I) (r : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    basedTailDiagram η X a r p ⟶ iterationTailBasedDiagram η X a r p :=
  PointedCGWH.PointedAtGeometry.diagramAtMap (projectionTailUnderlying η X a r) p

omit B in
/-- Every based projection right map is the actual whole native projection at that shifted stage. -/
theorem basedTailProjection_right (X : Cat.{u, v} I) (a : I) (r n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    ((basedTailProjection η X a r p).app n).right =
      (component ((projection η (r + n)).app X) a).right := rfl

/-- The original arbitrary-source cylinder deformation proves weakness at every
actual tail point. -/
theorem basedTailProjection_weakEquivalence (X : Cat.{u, v} I) (a : I) (r n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    WeakEquivalence ((basedTailProjection η X a r p).app n) :=
  (PointedCGWH.weakEquivalence_iff _).mpr
    ((PointedCGWH.weakEquivalence_iff (component ((projection η (r + n)).app X) a)).mp
      ((HomotopicalAlgebra.weakEquivalence_iff _).mpr
        (projection_component_weak η (r + n) X a)))

/-- Both original Type projection maps are defined at every actual tail point and every degree. -/
def basedTailProjectionTypeComponent (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (piNFunctor k).obj ((basedTailDiagram η X a r p).obj n) ≅
      (piNFunctor k).obj ((iterationTailBasedDiagram η X a r p).obj n) :=
  (piNEquivOfWeakEquivalence k ((basedTailProjection η X a r p).app n)
    (basedTailProjection_weakEquivalence η X a r n p)).toIso

/-- The whole Type projection forward function is the actual original homotopy map. -/
theorem basedTailProjectionTypeComponent_hom (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailProjectionTypeComponent η X a r k n p).hom =
      (piNFunctor k).map ((basedTailProjection η X a r p).app n) := by
  apply ConcreteCategory.hom_ext
  intro q
  exact piNEquivOfWeakEquivalence_apply k _ (basedTailProjection_weakEquivalence η X a r n p) q

/-- Both maps form an isomorphism of the complete original based Type diagrams. -/
def basedTailProjectionTypeIso (X : Cat.{u, v} I) (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    basedTailDiagram η X a r p ⋙ piNFunctor k ≅
      iterationTailBasedDiagram η X a r p ⋙ piNFunctor k :=
  NatIso.ofComponents (fun n => basedTailProjectionTypeComponent η X a r k n p)
    (fun f => by
      have h := (Functor.whiskerRight (basedTailProjection η X a r p) (piNFunctor k)).naturality f
      exact (congrArg (fun q => (piNFunctor k).map ((basedTailDiagram η X a r p).map f) ≫ q)
        (basedTailProjectionTypeComponent_hom η X a r k _ p)).trans
          (h.trans (congrArg (fun q => q ≫
            (piNFunctor k).map ((iterationTailBasedDiagram η X a r p).map f))
              (basedTailProjectionTypeComponent_hom η X a r k _ p).symm)))

/-- The full forward Type transformation is the original whole based projection homotopy map. -/
theorem basedTailProjectionTypeIso_hom (X : Cat.{u, v} I) (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailProjectionTypeIso η X a r k p).hom =
      Functor.whiskerRight (basedTailProjection η X a r p) (piNFunctor k) := by
  apply NatTrans.ext
  funext n
  exact basedTailProjectionTypeComponent_hom η X a r k n p

/-- Every genuine positive Group component keeps both actual weak-projection group maps. -/
def basedTailProjectionPositiveComponent (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (piNPositiveFunctor k).obj ((basedTailDiagram η X a r p).obj n) ≅
      (piNPositiveFunctor k).obj ((iterationTailBasedDiagram η X a r p).obj n) :=
  (piNPositiveMulEquivOfWeakEquivalence k ((basedTailProjection η X a r p).app n)
    (basedTailProjection_weakEquivalence η X a r n p)).toGrpIso

/-- The forward Group map is the original positive homotopy map of that exact projection. -/
theorem basedTailProjectionPositiveComponent_hom (X : Cat.{u, v} I) (a : I) (r k n : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailProjectionPositiveComponent η X a r k n p).hom =
      (piNPositiveFunctor k).map ((basedTailProjection η X a r p).app n) := by
  apply GrpCat.hom_ext
  ext q
  exact piNPositiveMulEquivOfWeakEquivalence_apply k _
    (basedTailProjection_weakEquivalence η X a r n p) q

/-- Both actual Group maps form an isomorphism of the complete original positive based diagrams. -/
def basedTailProjectionPositiveIso (X : Cat.{u, v} I) (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    basedTailDiagram η X a r p ⋙ piNPositiveFunctor k ≅
      iterationTailBasedDiagram η X a r p ⋙ piNPositiveFunctor k :=
  NatIso.ofComponents (fun n => basedTailProjectionPositiveComponent η X a r k n p)
    (fun f => by
      have h := (Functor.whiskerRight (basedTailProjection η X a r p)
        (piNPositiveFunctor k)).naturality f
      exact (congrArg (fun q =>
        (piNPositiveFunctor k).map ((basedTailDiagram η X a r p).map f) ≫ q)
          (basedTailProjectionPositiveComponent_hom η X a r k _ p)).trans
            (h.trans (congrArg (fun q => q ≫
              (piNPositiveFunctor k).map ((iterationTailBasedDiagram η X a r p).map f))
                (basedTailProjectionPositiveComponent_hom η X a r k _ p).symm)))

/-- The forward Group transformation is the original complete based projection group map. -/
theorem basedTailProjectionPositiveIso_hom (X : Cat.{u, v} I) (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    (basedTailProjectionPositiveIso η X a r k p).hom =
      Functor.whiskerRight (basedTailProjection η X a r p) (piNPositiveFunctor k) := by
  apply NatTrans.ext
  funext n
  exact basedTailProjectionPositiveComponent_hom η X a r k n p

namespace EvaluatedCylinder

variable {J : Type} [EnrichedCategory PointedCGWH.{u, v} J]

open PointedCGWH.EnrichedIntervalMappingCylinder

omit B in
private theorem scalarEndpointNaturality {A C : PointedCGWH.{u, v}}
    {T : PointedCGWH.{u, v}} (e : 𝟙_ PointedCGWH.{u, v} ⟶ T) (s : A ⟶ C) :
    ((λ_ A).inv ≫ e ▷ A) ≫ T ◁ s = s ≫ ((λ_ C).inv ≫ e ▷ C) := by
  rw [Category.assoc, ← whisker_exchange, ← Category.assoc,
    ← leftUnitor_inv_naturality, Category.assoc]

omit B in
private theorem scalarContractionNaturality {A C : PointedCGWH.{u, v}}
    {T : PointedCGWH.{u, v}} (e : T ⟶ 𝟙_ PointedCGWH.{u, v}) (s : A ⟶ C) :
    T ◁ s ≫ (e ▷ C ≫ (λ_ C).hom) = (e ▷ A ≫ (λ_ A).hom) ≫ s := by
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    leftUnitor_naturality, ← Category.assoc]

omit B in
/-- Evaluation retains the actual first-endpoint pushout and both native cylinder legs. -/
theorem componentPushout (f : Arrow (Cat.{u, v} I)) (a : I) :
    IsPushout (component (EnrichedIntervalCylinder.inclusion 0 f.left) a)
      (component f.hom a) (component (intervalLeg f) a) (component (targetLeg f) a) :=
  (IsPushout.of_hasPushout (EnrichedIntervalCylinder.inclusion 0 f.left) f.hom).map
    (evaluation a)

omit B in
/-- Every endpoint component is natural even between independently indexed native diagrams. -/
theorem endpoint_component_naturality (i : Fin 2)
    (X : Cat.{u, v} I) (Y : Cat.{u, v} J) (a : I) (b : J)
    (s : X.toEnrichedFunctor.obj a ⟶ Y.toEnrichedFunctor.obj b) :
    (component (EnrichedIntervalCylinder.inclusion i X) a :
        X.toEnrichedFunctor.obj a ⟶ IntervalCoefficient.interval ⊗ X.toEnrichedFunctor.obj a) ≫
        IntervalCoefficient.interval ◁ s =
      s ≫ (component (EnrichedIntervalCylinder.inclusion i Y) b :
        Y.toEnrichedFunctor.obj b ⟶ IntervalCoefficient.interval ⊗ Y.toEnrichedFunctor.obj b) := by
  exact (congrArg (fun q => q ≫ IntervalCoefficient.interval ◁ s)
    (EnrichedIntervalCylinder.inclusion_component i X a)).trans
      ((scalarEndpointNaturality (IntervalCoefficient.endpoint i) s).trans
        (congrArg (fun q => s ≫ q)
          (EnrichedIntervalCylinder.inclusion_component i Y b).symm))

omit B in
/-- The original contraction component is natural between the same arbitrary level objects. -/
theorem contraction_component_naturality
    (X : Cat.{u, v} I) (Y : Cat.{u, v} J) (a : I) (b : J)
    (s : X.toEnrichedFunctor.obj a ⟶ Y.toEnrichedFunctor.obj b) :
    IntervalCoefficient.interval ◁ s ≫
        (component (EnrichedIntervalCylinder.projection Y) b :
          IntervalCoefficient.interval ⊗ Y.toEnrichedFunctor.obj b ⟶ Y.toEnrichedFunctor.obj b) =
      (component (EnrichedIntervalCylinder.projection X) a :
          IntervalCoefficient.interval ⊗ X.toEnrichedFunctor.obj a ⟶ X.toEnrichedFunctor.obj a) ≫
        s := by
  exact (congrArg (fun q => IntervalCoefficient.interval ◁ s ≫ q)
    (EnrichedIntervalCylinder.projection_component Y b)).trans
      ((scalarContractionNaturality IntervalCoefficient.augmentation s).trans
        (congrArg (fun q => q ≫ s)
          (EnrichedIntervalCylinder.projection_component X a).symm))

/-- A genuine evaluated arrow square induces the map of the same actual cylinder pushouts. -/
def comparisonMap (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t = s ≫ component g.hom b) :
    (object f).toEnrichedFunctor.obj a ⟶ (object g).toEnrichedFunctor.obj b :=
  (componentPushout f a).desc
    (IntervalCoefficient.interval ◁ s ≫ component (intervalLeg g) b)
    (t ≫ component (targetLeg g) b) (by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ component (intervalLeg g) b)
          (endpoint_component_naturality 0 f.left g.left a b s)).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun q => s ≫ q) (componentPushout g b).w).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun q => q ≫ component (targetLeg g) b) h.symm).trans
                    (Category.assoc _ _ _)))))))

omit B in
/-- The complete cylinder comparison preserves the original interval leg and scalar map. -/
theorem intervalLeg_comparisonMap
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t = s ≫ component g.hom b) :
    component (intervalLeg f) a ≫ comparisonMap f g a b s t h =
      IntervalCoefficient.interval ◁ s ≫ component (intervalLeg g) b :=
  (componentPushout f a).inl_desc _ _ _

omit B in
/-- Its complete target leg keeps the entire original target component map. -/
theorem targetLeg_comparisonMap
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t = s ≫ component g.hom b) :
    component (targetLeg f) a ≫ comparisonMap f g a b s t h =
      t ≫ component (targetLeg g) b :=
  (componentPushout f a).inr_desc _ _ _

omit B in
/-- The second original endpoint is preserved by the same full cylinder comparison. -/
theorem source_comparisonMap
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t = s ≫ component g.hom b) :
    component (source f) a ≫ comparisonMap f g a b s t h =
      s ≫ component (source g) b := by
  have hf : component (source f) a = component (EnrichedIntervalCylinder.inclusion 1 f.left) a ≫
      component (intervalLeg f) a :=
    component_comp (EnrichedIntervalCylinder.inclusion 1 f.left) (intervalLeg f) a
  have hg : component (source g) b = component (EnrichedIntervalCylinder.inclusion 1 g.left) b ≫
      component (intervalLeg g) b :=
    component_comp (EnrichedIntervalCylinder.inclusion 1 g.left) (intervalLeg g) b
  exact (congrArg (fun q => q ≫ comparisonMap f g a b s t h) hf).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => component (EnrichedIntervalCylinder.inclusion 1 f.left) a ≫ q)
        (intervalLeg_comparisonMap f g a b s t h)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ component (intervalLeg g) b)
              (endpoint_component_naturality 1 f.left g.left a b s)).trans
                ((Category.assoc _ _ _).trans (congrArg (fun q => s ≫ q) hg.symm))))))

omit B in
/-- Source and target isomorphisms retain the same evaluated target cylinder as a pushout. -/
theorem comparisonPushout
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    IsPushout (component (EnrichedIntervalCylinder.inclusion 0 f.left) a)
      (component f.hom a)
      (IntervalCoefficient.interval ◁ s.hom ≫ component (intervalLeg g) b)
      (t.hom ≫ component (targetLeg g) b) :=
  (componentPushout g b).of_iso' s (whiskerLeftIso IntervalCoefficient.interval s) t
    (Iso.refl ((object g).toEnrichedFunctor.obj b))
    (endpoint_component_naturality 0 f.left g.left a b s.hom).symm h.symm
    (Category.comp_id _).symm (Category.comp_id _).symm

/-- Both maps compare the actual native cylinder values at the two original indices. -/
def comparisonIso
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    (object f).toEnrichedFunctor.obj a ≅ (object g).toEnrichedFunctor.obj b :=
  (componentPushout f a).isoIsPushout _ _ (comparisonPushout f g a b s t h)

omit B in
/-- The isomorphism forward map is the same complete original pushout comparison map. -/
theorem comparisonIso_hom
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    (comparisonIso f g a b s t h).hom = comparisonMap f g a b s.hom t.hom h := by
  apply (componentPushout f a).hom_ext
  · exact ((componentPushout f a).inl_isoIsPushout_hom _ _
      (comparisonPushout f g a b s t h)).trans
        (intervalLeg_comparisonMap f g a b s.hom t.hom h).symm
  · exact ((componentPushout f a).inr_isoIsPushout_hom _ _
      (comparisonPushout f g a b s t h)).trans
        (targetLeg_comparisonMap f g a b s.hom t.hom h).symm

omit B in
/-- The inverse interval leg retains the same original inverse source component map. -/
theorem intervalLeg_comparisonIso_inv
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    component (intervalLeg g) b ≫ (comparisonIso f g a b s t h).inv =
      IntervalCoefficient.interval ◁ s.inv ≫ component (intervalLeg f) a := by
  have hs : CommSq (component (intervalLeg f) a)
      (IntervalCoefficient.interval ◁ s.hom) ((comparisonIso f g a b s t h).hom)
      (component (intervalLeg g) b) :=
    ⟨(congrArg (fun q => component (intervalLeg f) a ≫ q)
      (comparisonIso_hom f g a b s t h)).trans
        (intervalLeg_comparisonMap f g a b s.hom t.hom h)⟩
  exact (CommSq.vert_inv (g := whiskerLeftIso IntervalCoefficient.interval s)
    (h := comparisonIso f g a b s t h) hs).w

omit B in
/-- The inverse target leg is correlated with the same original inverse target component map. -/
theorem targetLeg_comparisonIso_inv
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    component (targetLeg g) b ≫ (comparisonIso f g a b s t h).inv =
      t.inv ≫ component (targetLeg f) a := by
  have hs : CommSq (component (targetLeg f) a) t.hom
      ((comparisonIso f g a b s t h).hom) (component (targetLeg g) b) :=
    ⟨(congrArg (fun q => component (targetLeg f) a ≫ q)
      (comparisonIso_hom f g a b s t h)).trans
        (targetLeg_comparisonMap f g a b s.hom t.hom h)⟩
  exact (CommSq.vert_inv (g := t) (h := comparisonIso f g a b s t h) hs).w

omit B in
/-- Both isomorphism directions use the same actual pushout maps and original inverse square. -/
theorem comparisonIso_inv
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    (comparisonIso f g a b s t h).inv =
      comparisonMap g f b a s.inv t.inv (CommSq.vert_inv (g := s) (h := t) ⟨h⟩).w := by
  apply (componentPushout g b).hom_ext
  · exact (intervalLeg_comparisonIso_inv f g a b s t h).trans
      (intervalLeg_comparisonMap g f b a s.inv t.inv _).symm
  · exact (targetLeg_comparisonIso_inv f g a b s t h).trans
      (targetLeg_comparisonMap g f b a s.inv t.inv _).symm

omit B in
private theorem intervalRetractionComponent (f : Arrow (Cat.{u, v} I)) (a : I) :
    component (intervalLeg f) a ≫ component (retraction f) a =
      component (EnrichedIntervalCylinder.projection f.left) a ≫ component f.hom a := by
  have h := congrArg (fun q => component q a) (intervalLeg_retraction f)
  simp only [component_comp] at h
  exact h

omit B in
private theorem targetRetractionComponent (f : Arrow (Cat.{u, v} I)) (a : I) :
    component (targetLeg f) a ≫ component (retraction f) a =
      𝟙 (f.right.toEnrichedFunctor.obj a) := by
  have h := congrArg (fun q => component q a) (targetLeg_retraction f)
  simp only [component_comp, component_id] at h
  exact h

omit B in
private theorem retractionSquareOnInterval
    {X Y M N S T A C : PointedCGWH.{u, v}}
    {i : X ⟶ M} {j : Y ⟶ N} {a : X ⟶ Y} {u : M ⟶ N}
    {r : M ⟶ A} {r' : N ⟶ C} {p : X ⟶ S} {p' : Y ⟶ T}
    {s : S ⟶ T} {f : S ⟶ A} {g : T ⟶ C} {t : A ⟶ C}
    (hi : i ≫ u = a ≫ j) (hj : j ≫ r' = p' ≫ g)
    (hp : a ≫ p' = p ≫ s) (hf : f ≫ t = s ≫ g) (hr : i ≫ r = p ≫ f) :
    i ≫ (u ≫ r') = i ≫ (r ≫ t) := by
  rw [← Category.assoc, hi, Category.assoc, hj, ← Category.assoc, hp,
    Category.assoc, ← hf, ← Category.assoc, ← hr, Category.assoc]

omit B in
/-- The whole mixed-index cylinder map preserves the original contraction retractions. -/
theorem comparisonMap_retraction
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t = s ≫ component g.hom b) :
    comparisonMap f g a b s t h ≫ component (retraction g) b =
      component (retraction f) a ≫ t := by
  apply (componentPushout f a).hom_ext
  · exact retractionSquareOnInterval (intervalLeg_comparisonMap f g a b s t h)
      (intervalRetractionComponent g b)
      (contraction_component_naturality f.left g.left a b s) h
      (intervalRetractionComponent f a)
  · calc
      component (targetLeg f) a ≫
          (comparisonMap f g a b s t h ≫ component (retraction g) b) =
          (component (targetLeg f) a ≫ comparisonMap f g a b s t h) ≫
            component (retraction g) b := (Category.assoc _ _ _).symm
      _ = (t ≫ component (targetLeg g) b) ≫ component (retraction g) b :=
          congrArg (fun q => q ≫ component (retraction g) b)
            (targetLeg_comparisonMap f g a b s t h)
      _ = t ≫ (component (targetLeg g) b ≫ component (retraction g) b) :=
          Category.assoc _ _ _
      _ = t ≫ 𝟙 _ := congrArg (fun q => t ≫ q) (targetRetractionComponent g b)
      _ = t := Category.comp_id _
      _ = 𝟙 _ ≫ t := (Category.id_comp _).symm
      _ = (component (targetLeg f) a ≫ component (retraction f) a) ≫ t :=
          congrArg (fun q => q ≫ t) (targetRetractionComponent f a).symm
      _ = component (targetLeg f) a ≫ (component (retraction f) a ≫ t) :=
          Category.assoc _ _ _

omit B in
/-- The forward isomorphism preserves that same full original contraction projection. -/
theorem comparisonIso_retraction
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    (comparisonIso f g a b s t h).hom ≫ component (retraction g) b =
      component (retraction f) a ≫ t.hom :=
  (congrArg (fun q => q ≫ component (retraction g) b)
    (comparisonIso_hom f g a b s t h)).trans
      (comparisonMap_retraction f g a b s.hom t.hom h)

omit B in
/-- The inverse preserves the same inverse target component and original contraction. -/
theorem comparisonIso_inv_retraction
    (f : Arrow (Cat.{u, v} I)) (g : Arrow (Cat.{u, v} J)) (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ≅ g.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ≅ g.right.toEnrichedFunctor.obj b)
    (h : component f.hom a ≫ t.hom = s.hom ≫ component g.hom b) :
    (comparisonIso f g a b s t h).inv ≫ component (retraction f) a =
      component (retraction g) b ≫ t.inv :=
  (CommSq.vert_inv (g := comparisonIso f g a b s t h) (h := t)
    ⟨(comparisonIso_retraction f g a b s t h).symm⟩).w.symm

omit B in
/-- Every actual native Arrow morphism retains its complete evaluated source square. -/
theorem arrow_component_square {f g : Arrow (Cat.{u, v} I)} (h : f ⟶ g) (a : I) :
    component f.hom a ≫ component h.right a = component h.left a ≫ component g.hom a := by
  have hw := congrArg (fun q => component q a) (Arrow.w h)
  simp only [component_comp] at hw
  exact hw.symm

/-- The original native cylinder Arrow map evaluated at its actual index. -/
def nativeMapValue {f g : Arrow (Cat.{u, v} I)} (h : f ⟶ g) (a : I) :
    (object f).toEnrichedFunctor.obj a ⟶ (object g).toEnrichedFunctor.obj a :=
  component (EnrichedIntervalMappingCylinder.map h) a

omit B in
/-- Evaluating retains the entire original native cylinder map as its literal value. -/
theorem nativeMapValue_original {f g : Arrow (Cat.{u, v} I)} (h : f ⟶ g) (a : I) :
    nativeMapValue h a = component (EnrichedIntervalMappingCylinder.map h) a := rfl

omit B in
/-- The whole original native Arrow map preserves its actual evaluated interval leg. -/
theorem nativeIntervalMapComponent {f g : Arrow (Cat.{u, v} I)}
    (h : f ⟶ g) (a : I) :
    component (intervalLeg f) a ≫ nativeMapValue h a =
      IntervalCoefficient.interval ◁ component h.left a ≫ component (intervalLeg g) a := by
  have hw := congrArg (fun q => component q a) (intervalLeg_map h)
  simp only [component_comp, tensorLeftMap_component] at hw
  exact hw

omit B in
/-- The same native Arrow map preserves its complete evaluated target leg. -/
theorem nativeTargetMapComponent {f g : Arrow (Cat.{u, v} I)}
    (h : f ⟶ g) (a : I) :
    component (targetLeg f) a ≫ nativeMapValue h a =
      component h.right a ≫ component (targetLeg g) a := by
  have hw := congrArg (fun q => component q a) (targetLeg_map h)
  simp only [component_comp] at hw
  exact hw

omit B in
/-- The actual squares of two maps and two comparisons give the complete square on a leg. -/
theorem mappedLegSquare
    {A C A' C' P R P' R' : PointedCGWH.{u, v}}
    {a : A ⟶ C} {b : A' ⟶ C'} {s : A ⟶ A'} {t : C ⟶ C'}
    {i : A ⟶ P} {j : C ⟶ R} {i' : A' ⟶ P'} {j' : C' ⟶ R'}
    {u : P ⟶ R} {v : P' ⟶ R'} {c : P ⟶ P'} {d : R ⟶ R'}
    (hu : i ≫ u = a ≫ j) (hv : i' ≫ v = b ≫ j')
    (hc : i ≫ c = s ≫ i') (hd : j ≫ d = t ≫ j')
    (h : a ≫ t = s ≫ b) : i ≫ (u ≫ d) = i ≫ (c ≫ v) := by
  rw [← Category.assoc, hu, Category.assoc, hd, ← Category.assoc, h,
    Category.assoc, ← hv, ← Category.assoc, ← hc, Category.assoc]

section NativeMapNaturality

attribute [local irreducible] nativeMapValue comparisonMap

omit B in
/-- Both original evaluated pushout legs determine the full cylinder map. -/
theorem componentHomExt
    (f : Arrow (Cat.{u, v} I)) (a : I) {T : PointedCGWH.{u, v}}
    {k l : (object f).toEnrichedFunctor.obj a ⟶ T}
    (hInterval : component (intervalLeg f) a ≫ k = component (intervalLeg f) a ≫ l)
    (hTarget : component (targetLeg f) a ≫ k = component (targetLeg f) a ≫ l) : k = l :=
  (componentPushout f a).hom_ext hInterval hTarget

omit B in
private theorem comparisonIntervalLegNaturality
    {f g : Arrow (Cat.{u, v} I)} {f' g' : Arrow (Cat.{u, v} J)}
    (α : f ⟶ g) (β : f' ⟶ g') (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ f'.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ f'.right.toEnrichedFunctor.obj b)
    (s' : g.left.toEnrichedFunctor.obj a ⟶ g'.left.toEnrichedFunctor.obj b)
    (t' : g.right.toEnrichedFunctor.obj a ⟶ g'.right.toEnrichedFunctor.obj b)
    (hf : component f.hom a ≫ t = s ≫ component f'.hom b)
    (hg : component g.hom a ≫ t' = s' ≫ component g'.hom b)
    (hs : component α.left a ≫ s' = s ≫ component β.left b) :
    component (intervalLeg f) a ≫
        (nativeMapValue α a ≫ comparisonMap g g' a b s' t' hg) =
      component (intervalLeg f) a ≫
        (comparisonMap f f' a b s t hf ≫ nativeMapValue β b) := by
  have hTensor : (IntervalCoefficient.interval ◁ component α.left a) ≫
      (IntervalCoefficient.interval ◁ s') =
    (IntervalCoefficient.interval ◁ s) ≫ (IntervalCoefficient.interval ◁ component β.left b) :=
    (whiskerLeft_comp IntervalCoefficient.interval (component α.left a) s').symm.trans
      ((congrArg (fun q => IntervalCoefficient.interval ◁ q) hs).trans
        (whiskerLeft_comp IntervalCoefficient.interval s (component β.left b)))
  exact mappedLegSquare
    (nativeIntervalMapComponent α a) (nativeIntervalMapComponent β b)
    (intervalLeg_comparisonMap f f' a b s t hf)
    (intervalLeg_comparisonMap g g' a b s' t' hg) hTensor

omit B in
private theorem comparisonTargetLegNaturality
    {f g : Arrow (Cat.{u, v} I)} {f' g' : Arrow (Cat.{u, v} J)}
    (α : f ⟶ g) (β : f' ⟶ g') (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ f'.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ f'.right.toEnrichedFunctor.obj b)
    (s' : g.left.toEnrichedFunctor.obj a ⟶ g'.left.toEnrichedFunctor.obj b)
    (t' : g.right.toEnrichedFunctor.obj a ⟶ g'.right.toEnrichedFunctor.obj b)
    (hf : component f.hom a ≫ t = s ≫ component f'.hom b)
    (hg : component g.hom a ≫ t' = s' ≫ component g'.hom b)
    (ht : component α.right a ≫ t' = t ≫ component β.right b) :
    component (targetLeg f) a ≫
        (nativeMapValue α a ≫ comparisonMap g g' a b s' t' hg) =
      component (targetLeg f) a ≫
        (comparisonMap f f' a b s t hf ≫ nativeMapValue β b) :=
  mappedLegSquare (nativeTargetMapComponent α a) (nativeTargetMapComponent β b)
    (targetLeg_comparisonMap f f' a b s t hf)
    (targetLeg_comparisonMap g g' a b s' t' hg) ht

omit B in
/-- The complete actual Arrow maps are natural for every mixed-index cylinder comparison. -/
theorem comparisonMap_naturality
    {f g : Arrow (Cat.{u, v} I)} {f' g' : Arrow (Cat.{u, v} J)}
    (α : f ⟶ g) (β : f' ⟶ g') (a : I) (b : J)
    (s : f.left.toEnrichedFunctor.obj a ⟶ f'.left.toEnrichedFunctor.obj b)
    (t : f.right.toEnrichedFunctor.obj a ⟶ f'.right.toEnrichedFunctor.obj b)
    (s' : g.left.toEnrichedFunctor.obj a ⟶ g'.left.toEnrichedFunctor.obj b)
    (t' : g.right.toEnrichedFunctor.obj a ⟶ g'.right.toEnrichedFunctor.obj b)
    (hf : component f.hom a ≫ t = s ≫ component f'.hom b)
    (hg : component g.hom a ≫ t' = s' ≫ component g'.hom b)
    (hs : component α.left a ≫ s' = s ≫ component β.left b)
    (ht : component α.right a ≫ t' = t ≫ component β.right b) :
    nativeMapValue α a ≫ comparisonMap g g' a b s' t' hg =
      comparisonMap f f' a b s t hf ≫ nativeMapValue β b := by
  have hInterval := comparisonIntervalLegNaturality α β a b s t s' t' hf hg hs
  have hTarget := comparisonTargetLegNaturality α β a b s t s' t' hf hg ht
  exact componentHomExt f a
    (k := nativeMapValue α a ≫ comparisonMap g g' a b s' t' hg)
    (l := comparisonMap f f' a b s t hf ≫ nativeMapValue β b)
    hInterval hTarget

end NativeMapNaturality

end EvaluatedCylinder

end PointedCGWH.EnrichedCoaugmentationTelescope
