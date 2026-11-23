/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantHomotopyGeneratorDetection
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPushout
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import MathlibExt.AlgebraicTopology.ModelCategory.ContinuousCofibrationColimit
import MathlibExt.AlgebraicTopology.ModelCategory.InverseOrdinalInjectiveLimit
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Combinatorial
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftKanWeak
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Adjunction.Evaluation
import MathlibExt.CategoryTheory.MorphismProperty.CoproductCellDecomposition
import MathlibExt.CategoryTheory.MorphismProperty.OriginalAttachmentCoordinates
import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Original generating endpoints and cofibrant cell approximations

The cofibrant approximation of an original cell span uses the original Q
counit and both original I-factor maps. Its comparison with the original
pushout is weak by the actual left proper model. Neither endpoint of the
generating map is assumed cofibrant.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w u v t

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open scoped SSet.modelCategoryQuillen



namespace HomotopicalAlgebra.CellularGeneratingEndpointDetection

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements CofibrantHomotopyGeneratorDetection

/-- The whole original span is approximated by the original Q and the two
original generated I factorizations of its actual leg composites. -/
def generatedSpan (F : WalkingSpan ⥤ C) : CofibrantSpanReplacement F := by
  let q := (counit d).app (F.obj WalkingSpan.zero)
  let left := d.cofibrantFactorizationData.factorizationData (q ≫ F.map WalkingSpan.Hom.fst)
  let right := d.cofibrantFactorizationData.factorizationData (q ≫ F.map WalkingSpan.Hom.snd)
  let P := span left.i right.i
  let p : P ⟶ F := spanHomMk q left.p right.p left.fac right.fac
  exact {
    Q := P
    counit := p
    isCofibrant_zero := Q_isCofibrant d (F.obj WalkingSpan.zero)
    cofibration_fst := (cofibration_iff _).mpr left.hi
    cofibration_snd := (cofibration_iff _).mpr right.hi
    counit_app_mem_trivialFibrations := by
      rintro (_ | _ | _)
      · exact counit_trivialFibration d (F.obj WalkingSpan.zero)
      · exact left.hp
      · exact right.hp }

/-- The original source approximation is exactly the chosen original Q object. -/
theorem generatedSpan_zero (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).Q.obj WalkingSpan.zero = (Q d).obj (F.obj WalkingSpan.zero) := rfl

/-- The entire original source comparison is the original generated Q counit. -/
theorem generatedSpan_counit_zero (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).counit.app WalkingSpan.zero =
      (counit d).app (F.obj WalkingSpan.zero) := rfl

/-- The actual first target is the original I middle object at the actual original first leg. -/
theorem generatedSpan_left (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).Q.obj WalkingSpan.left =
      d.cofibrantFactorizationData.Z.obj (Arrow.mk
        ((counit d).app (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.fst)) := rfl

/-- The actual second target is the same original I factory at the original second leg. -/
theorem generatedSpan_right (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).Q.obj WalkingSpan.right =
      d.cofibrantFactorizationData.Z.obj (Arrow.mk
        ((counit d).app (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.snd)) := rfl

/-- The complete first inclusion retains its original I factor arrow. -/
theorem generatedSpan_fst (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).Q.map WalkingSpan.Hom.fst =
      d.cofibrantFactorizationData.i.app (Arrow.mk
        ((counit d).app (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.fst)) := rfl

/-- The complete second inclusion retains its original I factor arrow. -/
theorem generatedSpan_snd (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).Q.map WalkingSpan.Hom.snd =
      d.cofibrantFactorizationData.i.app (Arrow.mk
        ((counit d).app (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.snd)) := rfl

/-- The complete first target comparison retains its original trivial-fibration I factor. -/
theorem generatedSpan_counit_left (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).counit.app WalkingSpan.left =
      d.cofibrantFactorizationData.p.app (Arrow.mk
        ((counit d).app (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.fst)) := rfl

/-- The complete second target comparison retains its original trivial-fibration I factor. -/
theorem generatedSpan_counit_right (F : WalkingSpan ⥤ C) :
    (generatedSpan d F).counit.app WalkingSpan.right =
      d.cofibrantFactorizationData.p.app (Arrow.mk
        ((counit d).app (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.snd)) := rfl

/-- Every original generating cofibration is a cofibration in the actual original model. -/
theorem original_I_cofibration (i : d.I.toSet) : Cofibration i.1.hom := by
  apply (cofibration_iff _).mpr
  rw [← trivialFibrations_llp, ← d.I_rlp]
  exact (MorphismProperty.le_llp_rlp d.I) _ i.2

/-- The actual generated span-to-pushout comparison is weak whenever the
original first leg is a cofibration, including arbitrary noncofibrant endpoints. -/
theorem generatedSpan_comparison_weak [IsLeftProper C]
    (F : WalkingSpan ⥤ C) [Cofibration (F.map WalkingSpan.Hom.fst)] :
    WeakEquivalence (generatedSpan d F).toPushout := by
  let _ : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    d.hasFunctorialFactorizationCofibrationsTrivialFibrations
  exact ((generatedSpan d F).weakEquivalence_homotopyPushoutComparison_iff).mp
    (weakEquivalence_homotopyPushoutComparison_of_leftProper_fst F)

/-- The original raw source functor takes each actual original pushout to
the corresponding actual pullback of original right-frame maps. -/
theorem raw_pullback_of_pushout {A B X Y : C} {i : A ⟶ B} {a : A ⟶ X}
    {b : B ⟶ Y} {j : X ⟶ Y} (sq : IsPushout i a b j) (Z : C) :
    IsPullback (rawPrecomp d b Z) (rawPrecomp d j Z)
      (rawPrecomp d i Z) (rawPrecomp d a Z) := by
  let F := (rawBifunctor d).flip.obj Z
  let _ : PreservesLimitsOfSize.{0, 0} F := rawSource_preservesLimits d Z
  exact (sq.op.map F).flip

/-- Mapping out of the actual original initial object is terminal in every
original right-frame degree and as a whole simplicial set. -/
def rawInitialIsTerminal (Y : C) : IsTerminal (rawSpace d (⊥_ C) Y) := by
  let F := (rawBifunctor d).flip.obj Y
  let _ : PreservesLimitsOfSize.{0, 0} F := rawSource_preservesLimits d Y
  exact IsTerminal.isTerminalObj F (Opposite.op (⊥_ C)) initialIsInitial.op

/-- The initial-source case of the original weak mapping test needs no
condition on either original arrow endpoint. -/
theorem raw_initial_postcomp_weak {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (rawPostcomp d (⊥_ C) f) := by
  let _ : IsIso (rawPostcomp d (⊥_ C) f) :=
    isIso_of_isTerminal (rawInitialIsTerminal d X) (rawInitialIsTerminal d Y) _
  exact (weakEquivalence_iff _).mpr
    (SSet.realizationWeakEquivalences.of_isIso (rawPostcomp d (⊥_ C) f))

/-- The original Kan mapping space is cofibrant in the actual opposite
model, with the same terminal map and the same simplicial coefficients. -/
theorem raw_space_op_cofibrant (A : C) [IsCofibrant A] (Z : C) :
    IsCofibrant (Opposite.op (rawSpace d A Z)) := by
  let _ : SSet.KanComplex (rawSpace d A Z) := rawSpace_kanComplex d A Z
  apply (isCofibrant_iff_of_isInitial (terminal.from (rawSpace d A Z)).op terminalIsTerminal.op).mpr
  rw [cofibration_op_iff]
  exact inferInstanceAs (IsFibrant (rawSpace d A Z))

/-- Three original weak mapping tests extend over an actual cofibrant
pushout. The actual opposite-model cube proves the fourth corner, so no
right-properness outcome for the mapping category is supplied. -/
theorem raw_pushout_postcomp_weak {K L M N : C} {i : K ⟶ L} {a : K ⟶ M}
    {b : L ⟶ N} {j : M ⟶ N} (sq : IsPushout i a b j)
    [Cofibration i] [IsCofibrant K] [IsCofibrant M]
    {X Y : C} (f : X ⟶ Y)
    (hK : WeakEquivalence (rawPostcomp d K f))
    (hL : WeakEquivalence (rawPostcomp d L f))
    (hM : WeakEquivalence (rawPostcomp d M f)) :
    WeakEquivalence (rawPostcomp d N f) := by
  let _ : Cofibration (rawPrecomp d i Y).op := (cofibration_op_iff _).mpr (rawPrecomp_fibration d i Y)
  let _ : Cofibration (rawPrecomp d i X).op := (cofibration_op_iff _).mpr (rawPrecomp_fibration d i X)
  let _ : IsCofibrant (Opposite.op (rawSpace d K Y)) := raw_space_op_cofibrant d K Y
  let _ : IsCofibrant (Opposite.op (rawSpace d K X)) := raw_space_op_cofibrant d K X
  let _ : IsCofibrant (Opposite.op (rawSpace d M Y)) := raw_space_op_cofibrant d M Y
  let _ : IsCofibrant (Opposite.op (rawSpace d M X)) := raw_space_op_cofibrant d M X
  let _ : WeakEquivalence (rawPostcomp d K f).op := (weakEquivalences_op_iff _).mpr hK
  let _ : WeakEquivalence (rawPostcomp d L f).op := (weakEquivalences_op_iff _).mpr hL
  let _ : WeakEquivalence (rawPostcomp d M f).op := (weakEquivalences_op_iff _).mpr hM
  have h : WeakEquivalence (rawPostcomp d N f).op :=
    weakEquivalence_map_of_isPushouts_of_cofibrant
      (raw_pullback_of_pushout d sq Y).op.flip (raw_pullback_of_pushout d sq X).op.flip
      (a := (rawPostcomp d K f).op) (b := (rawPostcomp d L f).op)
      (c := (rawPostcomp d M f).op) (d := (rawPostcomp d N f).op)
      (congrArg Quiver.Hom.op (raw_naturality d i f)).symm
      (congrArg Quiver.Hom.op (raw_naturality d a f)).symm
      (congrArg Quiver.Hom.op (raw_naturality d b f)).symm
      (congrArg Quiver.Hom.op (raw_naturality d j f)).symm
  exact (weakEquivalences_op_iff _).mp h

private theorem cofibrant_pushout {K L M N : C} {i : K ⟶ L} {a : K ⟶ M}
    {b : L ⟶ N} {j : M ⟶ N} (sq : IsPushout i a b j)
    [Cofibration i] [IsCofibrant M] : IsCofibrant N := by
  let _ : Cofibration j := (cofibration_iff _).mpr
    ((cofibrations C).of_isPushout sq.flip (mem_cofibrations i))
  exact isCofibrant_of_cofibration j

/-- The actual generated cell-span colimit is cofibrant, from its original
generated Q source and its original two I cofibration legs. -/
theorem generatedSpan_point_cofibrant (F : WalkingSpan ⥤ C) :
    IsCofibrant (generatedSpan d F).pushoutObj := by
  let R := generatedSpan d F
  let _ : IsCofibrant (R.Q.obj WalkingSpan.zero) := R.isCofibrant_zero
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.fst) := R.cofibration_fst
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.snd) := R.cofibration_snd
  let _ : IsCofibrant (R.Q.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (R.Q.map WalkingSpan.Hom.snd)
  exact cofibrant_pushout (IsPushout.of_isColimit_cocone (colimit.isColimit R.Q))

/-- The original endpoint tests extend across every actual single-cell
attachment to a cofibrant stage. Both original cell endpoints may be
noncofibrant; all three original Q/I comparison maps and the actual caller
pushout cocone are used to return from the cofibrant approximation. -/
theorem original_cell_postcomp_weak [IsLeftProper C]
    {K L M N : C} {i : K ⟶ L} {a : K ⟶ M} {b : L ⟶ N} {j : M ⟶ N}
    (sq : IsPushout i a b j) [Cofibration i] [IsCofibrant M]
    {X Y : C} (f : X ⟶ Y)
    (hK : IsIso (GeneratedRightMappingEnrichment.postcomp d K f))
    (hL : IsIso (GeneratedRightMappingEnrichment.postcomp d L f))
    (hM : WeakEquivalence (rawPostcomp d M f)) :
    WeakEquivalence (rawPostcomp d N f) := by
  let F := span i a
  let _ : Cofibration (F.map WalkingSpan.Hom.fst) := inferInstanceAs (Cofibration i)
  let R := generatedSpan d F
  let _ : IsCofibrant (R.Q.obj WalkingSpan.zero) := R.isCofibrant_zero
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.fst) := R.cofibration_fst
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.snd) := R.cofibration_snd
  let _ : IsCofibrant (R.Q.obj WalkingSpan.left) :=
    isCofibrant_of_cofibration (R.Q.map WalkingSpan.Hom.fst)
  let _ : IsCofibrant (R.Q.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (R.Q.map WalkingSpan.Hom.snd)
  let _ : IsCofibrant R.pushoutObj := generatedSpan_point_cofibrant d F
  let _ : IsCofibrant N := cofibrant_pushout sq
  have hOriginalM : IsIso (GeneratedRightMappingEnrichment.postcomp d M f) :=
    (nativePostcomp_iff_raw d M f).mpr hM
  have hCorner (k : WalkingSpan) : weakEquivalences C (R.counit.app k) :=
    (R.counit_app_mem_trivialFibrations k).2
  have hR0 : WeakEquivalence (rawPostcomp d (R.Q.obj WalkingSpan.zero) f) :=
    (nativePostcomp_iff_raw d _ f).mp
      ((nativePostcomp_weak_source_iff d (R.counit.app WalkingSpan.zero) (hCorner _) f).mpr hK)
  have hRL : WeakEquivalence (rawPostcomp d (R.Q.obj WalkingSpan.left) f) :=
    (nativePostcomp_iff_raw d _ f).mp
      ((nativePostcomp_weak_source_iff d (R.counit.app WalkingSpan.left) (hCorner _) f).mpr hL)
  have hRR : WeakEquivalence (rawPostcomp d (R.Q.obj WalkingSpan.right) f) :=
    (nativePostcomp_iff_raw d _ f).mp
      ((nativePostcomp_weak_source_iff d (R.counit.app WalkingSpan.right) (hCorner _) f).mpr hOriginalM)
  have hRP : WeakEquivalence (rawPostcomp d R.pushoutObj f) :=
    raw_pushout_postcomp_weak d (IsPushout.of_isColimit_cocone (colimit.isColimit R.Q)) f hR0 hRL hRR
  let e : colimit F ≅ N := (colimit.isColimit F).coconePointUniqueUpToIso sq.isColimit
  let t : R.pushoutObj ⟶ N := R.toPushout ≫ e.hom
  have ht : weakEquivalences C t := (weakEquivalences C).comp_mem _ _
    ((weakEquivalence_iff _).mp (generatedSpan_comparison_weak d F))
    ((weakEquivalences C).of_isIso e.hom)
  exact (nativePostcomp_iff_raw d N f).mp
    ((nativePostcomp_weak_source_iff d t ht f).mp ((nativePostcomp_iff_raw d R.pushoutObj f).mpr hRP))

section OriginalInverseDiagrams

variable {J : Type w} [Category.{w} J]

/-- The entire original inverse raw mapping diagram retains the original
source diagram and every original source map. -/
def rawTower (F : J ⥤ C) (Z : C) : Jᵒᵖ ⥤ SSet.{v} :=
  F.op ⋙ (rawBifunctor d).flip.obj Z

/-- Every original target arrow induces its original map of whole inverse diagrams. -/
def rawTowerMap (F : J ⥤ C) {X Y : C} (f : X ⟶ Y) : rawTower d F X ⟶ rawTower d F Y :=
  Functor.whiskerLeft F.op ((rawBifunctor d).flip.map f)

/-- Every coefficient of the complete inverse-diagram map is the original raw target function. -/
theorem rawTowerMap_app (F : J ⥤ C) {X Y : C} (f : X ⟶ Y) (j : Jᵒᵖ) :
    (rawTowerMap d F f).app j = rawPostcomp d (F.obj j.unop) f := rfl

/-- Every actual caller source cocone gives the whole original inverse mapping cone. -/
def rawCone {F : J ⥤ C} (c : Cocone F) (Z : C) : Cone (rawTower d F Z) :=
  ((rawBifunctor d).flip.obj Z).mapCone c.op

/-- The complete original mapping cone keeps every original caller leg. -/
theorem rawCone_π {F : J ⥤ C} (c : Cocone F) (Z : C) (j : Jᵒᵖ) :
    (rawCone d c Z).π.app j = rawPrecomp d (c.ι.app j.unop) Z := rfl

/-- Original source continuity retains the caller's full actual limit universal property. -/
def rawConeIsLimit {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c) (Z : C) :
    IsLimit (rawCone d c Z) := by
  let _ : PreservesLimitsOfSize.{w, w} ((rawBifunctor d).flip.obj Z) := rawSource_preservesLimits d Z
  exact isLimitOfPreserves _ hc.op

/-- The coefficient lift enlarges only the simplicial value universe,
retaining the original source diagram and its original inverse maps. -/
def liftedRawTower (F : J ⥤ C) (Z : C) : Jᵒᵖ ⥤ SSet.{max w v} :=
  rawTower d F Z ⋙ SSet.uliftFunctor.{w, v}

/-- The same entire original target map is lifted degree by degree. -/
def liftedRawTowerMap (F : J ⥤ C) {X Y : C} (f : X ⟶ Y) :
    liftedRawTower d F X ⟶ liftedRawTower d F Y :=
  Functor.whiskerRight (rawTowerMap d F f) SSet.uliftFunctor.{w, v}

/-- The original source cocone yields its full lifted inverse mapping cone. -/
def liftedRawCone {F : J ⥤ C} (c : Cocone F) (Z : C) : Cone (liftedRawTower d F Z) :=
  SSet.uliftFunctor.{w, v}.mapCone (rawCone d c Z)

private theorem sSetUlift_preservesLimits : PreservesLimitsOfSize.{w, w} SSet.uliftFunctor.{w, v} := by
  apply preservesLimits_of_evaluation
  intro n
  let _ : PreservesLimitsOfSize.{w, w} ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n) :=
    (evaluationAdjunctionRight (Type v) n).rightAdjoint_preservesLimits
  let e : SSet.uliftFunctor.{w, v} ⋙ (evaluation SimplexCategoryᵒᵖ (Type (max w v))).obj n ≅
      (evaluation SimplexCategoryᵒᵖ (Type v)).obj n ⋙ CategoryTheory.uliftFunctor.{w, v} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; ext x; rfl)
  exact preservesLimits_of_natIso e.symm

/-- The coefficient lift preserves the original actual limiting cone. -/
def liftedRawConeIsLimit {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c) (Z : C) :
    IsLimit (liftedRawCone d c Z) := by
  let _ : PreservesLimitsOfSize.{w, w} SSet.uliftFunctor.{w, v} := sSetUlift_preservesLimits
  exact isLimitOfPreserves _ (rawConeIsLimit d c hc Z)

/-- The entire caller-cone square retains the lifted original target and
source functions, with every original source leg unchanged. -/
theorem liftedRawCone_naturality {F : J ⥤ C} (c : Cocone F) {X Y : C} (f : X ⟶ Y) (j : Jᵒᵖ) :
    SSet.uliftFunctor.{w, v}.map (rawPostcomp d c.pt f) ≫ (liftedRawCone d c Y).π.app j =
      (liftedRawCone d c X).π.app j ≫ (liftedRawTowerMap d F f).app j := by
  change SSet.uliftFunctor.map (rawPostcomp d c.pt f) ≫
      SSet.uliftFunctor.map (rawPrecomp d (c.ι.app j.unop) Y) =
    SSet.uliftFunctor.map (rawPrecomp d (c.ι.app j.unop) X) ≫
      SSet.uliftFunctor.map (rawPostcomp d (F.obj j.unop) f)
  exact (SSet.uliftFunctor.map_comp _ _).symm.trans
    ((SSet.uliftFunctor.congr_map (raw_naturality d (c.ι.app j.unop) f).symm).trans
      (SSet.uliftFunctor.map_comp _ _))

end OriginalInverseDiagrams

/-- The same original raw Kan mapping map is weak exactly when its
coefficient universe lift is weak. The original Hom and working universes
remain independent. -/
theorem lifted_rawPostcomp_weak_iff (A : C) [IsCofibrant A] {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (SSet.uliftFunctor.{w, v}.map (rawPostcomp d A f)) ↔
      WeakEquivalence (rawPostcomp d A f) := by
  let _ : SSet.KanComplex (rawSpace d A X) := rawSpace_kanComplex d A X
  let _ : SSet.KanComplex (rawSpace d A Y) := rawSpace_kanComplex d A Y
  let _ : SSet.KanComplex (SSet.uliftFunctor.{w, v}.obj (rawSpace d A X)) :=
    SSet.kanComplex_ulift (rawSpace d A X)
  let _ : SSet.KanComplex (SSet.uliftFunctor.{w, v}.obj (rawSpace d A Y)) :=
    SSet.kanComplex_ulift (rawSpace d A Y)
  have hBase : WeakEquivalence (rawPostcomp d A f) ↔ SSet.realizationWeakEquivalences (rawPostcomp d A f) :=
    weakEquivalence_iff (rawPostcomp d A f)
  have hLift : WeakEquivalence (SSet.uliftFunctor.{w, v}.map (rawPostcomp d A f)) ↔
      SSet.realizationWeakEquivalences (SSet.uliftFunctor.{w, v}.map (rawPostcomp d A f)) :=
    weakEquivalence_iff (SSet.uliftFunctor.{w, v}.map (rawPostcomp d A f))
  exact hLift.trans
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence _).symm.trans
      ((SSet.KanComplex.W_ulift_map_iff (rawPostcomp d A f)).trans
        ((SSet.KanComplex.W_iff_realizationWeakEquivalence _).trans hBase.symm)))

section ContinuousInverseDiagrams

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
/-- Source continuity and coefficient lifting preserve every original
proper-limit cone in the complete inverse mapping diagram. -/
theorem liftedRawTower_continuous (F : J ⥤ C) [F.IsWellOrderContinuous] (Z : C) :
    (liftedRawTower d F Z).rightOp.IsWellOrderContinuous := by
  let H := (rawBifunctor d).flip.obj Z ⋙ SSet.uliftFunctor.{w, v}
  let _ : PreservesLimitsOfSize.{w, w} ((rawBifunctor d).flip.obj Z) := rawSource_preservesLimits d Z
  let _ : PreservesLimitsOfSize.{w, w} SSet.uliftFunctor.{w, v} := sSetUlift_preservesLimits
  let _ : PreservesLimitsOfSize.{w, w} H := inferInstance
  let _ : PreservesColimitsOfSize.{w, w} H.rightOp := preservesColimitsOfSize_rightOp H
  let _ : PreservesWellOrderContinuousOfShape J H.rightOp :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  change (F ⋙ H.rightOp).IsWellOrderContinuous
  infer_instance

/-- Pointwise original weak mapping tests on a continuous cofibrant
cofibration source diagram pass to every actual caller colimit. Its full
inverse-limit model is constructed in the lifted simplicial universe. -/
theorem raw_continuous_postcomp_weak
    (F : J ⥤ C) [F.IsWellOrderContinuous] [∀ j : J, IsCofibrant (F.obj j)]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    {X Y : C} (f : X ⟶ Y) (hf : ∀ j : J, WeakEquivalence (rawPostcomp d (F.obj j) f))
    (c : Cocone F) (hc : IsColimit c) : WeakEquivalence (rawPostcomp d c.pt f) := by
  let _ : IsCofibrant c.pt := continuousCofibrationColimit_cofibrant F c hc
    (fun j hj => (cofibration_iff _).mp (hF j hj))
  let _ : (liftedRawTower d F X).rightOp.IsWellOrderContinuous := liftedRawTower_continuous d F X
  let _ : (liftedRawTower d F Y).rightOp.IsWellOrderContinuous := liftedRawTower_continuous d F Y
  have hBot (Z : C) : IsFibrant ((liftedRawTower d F Z).obj (Opposite.op (⊥ : J))) := by
    change SSet.KanComplex (SSet.uliftFunctor.{w, v}.obj (rawSpace d (F.obj ⊥) Z))
    let _ : SSet.KanComplex (rawSpace d (F.obj ⊥) Z) := rawSpace_kanComplex d (F.obj ⊥) Z
    exact SSet.kanComplex_ulift _
  have hStep (Z : C) (j : J) (hj : ¬IsMax j) :
      Fibration ((liftedRawTower d F Z).map (homOfLE (Order.le_succ j)).op) := by
    change Fibration (SSet.uliftFunctor.{w, v}.map
      (rawPrecomp d (F.map (homOfLE (Order.le_succ j))) Z))
    let _ : Cofibration (F.map (homOfLE (Order.le_succ j))) := hF j hj
    let _ : Fibration (rawPrecomp d (F.map (homOfLE (Order.le_succ j))) Z) :=
      rawPrecomp_fibration d _ Z
    exact SSet.modelCategoryQuillen.uliftFunctor_map_fibration
      (rawPrecomp d (F.map (homOfLE (Order.le_succ j))) Z)
  have hMap (j : Jᵒᵖ) : weakEquivalences SSet.{max w v} ((liftedRawTowerMap d F f).app j) :=
    (weakEquivalence_iff _).mp ((lifted_rawPostcomp_weak_iff d (F.obj j.unop) f).mpr (hf j.unop))
  have h : WeakEquivalence (SSet.uliftFunctor.{w, v}.map (rawPostcomp d c.pt f)) :=
    InverseOrdinalInjectiveLimit.weakEquivalence_of_continuous_inverse_isLimits
      (liftedRawTower d F X) (liftedRawTower d F Y) (liftedRawTowerMap d F f)
      (hBot X) (hBot Y) (hStep X) (hStep Y) hMap
      (liftedRawCone d c X) (liftedRawCone d c Y)
      (liftedRawConeIsLimit d c hc X) (liftedRawConeIsLimit d c hc Y)
      (SSet.uliftFunctor.{w, v}.map (rawPostcomp d c.pt f))
      (liftedRawCone_naturality d c f)
  exact (lifted_rawPostcomp_weak_iff d c.pt f).mp h

include d in
/-- Every original source map in a continuous cofibration diagram is a
cofibration, using the same original ordinal and actual cocone. -/
theorem continuous_source_map_cofibration
    (F : J ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    {i j : J} (g : i ⟶ j) : Cofibration (F.map g) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let _ : (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let c : (cofibrations C).TransfiniteCompositionOfShape J (colimit.ι F ⊥) := {
    F := F
    isoBot := Iso.refl _
    incl := (colimit.cocone F).ι
    isColimit := colimit.isColimit _
    fac := Category.id_comp _
    map_mem j hj := (cofibration_iff _).mp (hF j hj) }
  exact (cofibration_iff _).mpr (c.mem_map g)

include d in
/-- All actual stages remain cofibrant from the original bottom and every
original continuous cofibration transition. -/
theorem continuous_source_obj_cofibrant
    (F : J ⥤ C) [F.IsWellOrderContinuous] [IsCofibrant (F.obj ⊥)]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j)))) (j : J) :
    IsCofibrant (F.obj j) := by
  let _ : Cofibration (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)) :=
    continuous_source_map_cofibration d F hF _
  exact isCofibrant_of_cofibration (F.map (homOfLE bot_le : (⊥ : J) ⟶ j))

/-- The original initial and successor tests extend across every actual
limit stage of a continuous cofibrant source diagram. -/
theorem raw_continuous_pointwise
    (F : J ⥤ C) [F.IsWellOrderContinuous] [IsCofibrant (F.obj ⊥)]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    {X Y : C} (f : X ⟶ Y) (hBot : WeakEquivalence (rawPostcomp d (F.obj ⊥) f))
    (hSucc : ∀ j : J, ¬IsMax j → WeakEquivalence (rawPostcomp d (F.obj j) f) →
      WeakEquivalence (rawPostcomp d (F.obj (Order.succ j)) f)) :
    ∀ j : J, WeakEquivalence (rawPostcomp d (F.obj j) f) := by
  let _ : ∀ j : J, IsCofibrant (F.obj j) := fun j => continuous_source_obj_cofibrant d F hF j
  intro j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      obtain rfl := hj.eq_bot
      exact hBot
  | succ j hj ih => exact hSucc j hj ih
  | isSuccLimit j hj ih =>
      let _ : OrderBot (Set.Iio j) := { bot := ⟨⊥, hj.bot_lt⟩, bot_le _ := bot_le }
      let _ : SuccOrder (Set.Iio j) := SuccOrder.ofLinearWellFoundedLT _
      let r := (Set.principalSegIio j).monotone.functor
      let _ : (r ⋙ F).IsWellOrderContinuous := by
        exact inferInstanceAs
          ((((Set.principalSegIio j : Set.Iio j ≤i J).monotone.functor) ⋙ F).IsWellOrderContinuous)
      let _ : ∀ k : Set.Iio j, IsCofibrant ((r ⋙ F).obj k) :=
        fun k => inferInstanceAs (IsCofibrant (F.obj k.val))
      exact raw_continuous_postcomp_weak d (r ⋙ F)
        (fun k _ => continuous_source_map_cofibration d F hF (r.map (homOfLE (Order.le_succ k))))
        f (fun k => ih k.val k.property) ((Set.principalSegIio j).cocone F)
        (F.isColimitOfIsWellOrderContinuous j hj)

end ContinuousInverseDiagrams

/-- Single original generating-cell pushouts and actual isomorphisms. -/
def originalCells : MorphismProperty C := isomorphisms C ⊔ d.I.pushouts

private theorem originalCells_cofibrations : originalCells d ≤ cofibrations C := by
  have hI : d.I ≤ cofibrations C := by
    intro A B i hi
    exact (cofibration_iff _).mp (original_I_cofibration d ⟨Arrow.mk i, hi⟩)
  intro A B i hi
  rcases hi with hi | hi
  · let _ : IsIso i := hi
    exact (cofibrations C).of_isIso i
  · exact (cofibrations C).pushouts_le i ((pushouts_monotone hI) _ hi)

/-- Actual original generating-cell pushouts stay in the same class under
further cobase changes, including the original isomorphism cells. -/
theorem originalCells_pushouts_le : (originalCells d).pushouts ≤ originalCells d := by
  rintro A B i ⟨K, L, q, a, b, hq, sq⟩
  rcases hq with hq | hq
  · exact Or.inl ((isomorphisms C).of_isPushout sq hq)
  · exact Or.inr (d.I.pushouts.of_isPushout sq hq)

section OriginalCellChains

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The original endpoint tests extend across every continuous single-I-cell
chain, retaining the original source, endpoint, ordinal and actual cocone. -/
theorem originalCell_chain_postcomp_weak [IsLeftProper C]
    {A B : C} {u : A ⟶ B} (c : (originalCells d).TransfiniteCompositionOfShape J u)
    [IsCofibrant A] {X Y : C} (f : X ⟶ Y)
    (hTests : ∀ i : d.I.toSet,
      IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.left f) ∧
        IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.right f))
    (hA : WeakEquivalence (rawPostcomp d A f)) : WeakEquivalence (rawPostcomp d B f) := by
  let _ : c.F.IsWellOrderContinuous := c.isWellOrderContinuous
  let _ : Cofibration c.isoBot.inv := inferInstance
  let _ : IsCofibrant (c.F.obj ⊥) := isCofibrant_of_cofibration c.isoBot.inv
  have hF (j : J) (hj : ¬IsMax j) : Cofibration (c.F.map (homOfLE (Order.le_succ j))) :=
    (cofibration_iff _).mpr (originalCells_cofibrations d _ (c.map_mem j hj))
  let _ : ∀ j : J, IsCofibrant (c.F.obj j) := fun j => continuous_source_obj_cofibrant d c.F hF j
  have hBot : WeakEquivalence (rawPostcomp d (c.F.obj ⊥) f) :=
    (nativePostcomp_iff_raw d _ f).mp
      ((nativePostcomp_weak_source_iff d c.isoBot.hom
        ((weakEquivalences C).of_isIso c.isoBot.hom) f).mpr ((nativePostcomp_iff_raw d A f).mpr hA))
  have hSucc (j : J) (hj : ¬IsMax j) (h : WeakEquivalence (rawPostcomp d (c.F.obj j) f)) :
      WeakEquivalence (rawPostcomp d (c.F.obj (Order.succ j)) f) := by
    have hp := c.map_mem j hj
    rcases hp with hp | ⟨K, L, q, a, b, hq, sq⟩
    · let _ : IsIso (c.F.map (homOfLE (Order.le_succ j))) := hp
      exact (nativePostcomp_iff_raw d _ f).mp
        ((nativePostcomp_weak_source_iff d (c.F.map (homOfLE (Order.le_succ j)))
          ((weakEquivalences C).of_isIso _) f).mp ((nativePostcomp_iff_raw d _ f).mpr h))
    · let i : d.I.toSet := ⟨Arrow.mk q, hq⟩
      let _ : Cofibration q := original_I_cofibration d i
      exact original_cell_postcomp_weak d sq.flip f (hTests i).1 (hTests i).2 h
  exact raw_continuous_postcomp_weak d c.F hF f (raw_continuous_pointwise d c.F hF f hBot hSucc)
    (Cocone.mk B c.incl) c.isColimit

end OriginalCellChains

section OriginalCellCoordinates

variable [hCoproducts : HasCoproducts.{w} C] {α : Type t} {A B : α → C}
  (g : ∀ a, A a ⟶ B a) (hg : ∀ a, d.I (g a))
  {X Y : C} {u : X ⟶ Y} (c : AttachCells.{w} g u)
  [LinearOrder c.ι] [WellFoundedLT c.ι] [SuccOrder (CoproductCells.cellOrder c.ι)]

/-- The original attachment is the actual cobase change of its original
coordinate chain. Both supplied cofan isomorphisms, all their legs and the
original attachment square are retained at the literal original arrow. -/
def attachmentCoordinateChain :
    (originalCells d).TransfiniteCompositionOfShape (CoproductCells.cellOrder c.ι) u :=
  OriginalGeneratingCellCoordinates.attachmentCoordinateChain d.I g hg c

end OriginalCellCoordinates

/-- Every actual original attachment has a continuous single-cell history
on the same original source and endpoint, in its original working universe. -/
theorem attachmentHasOriginalCoordinateHistory
    [HasCoproducts.{w} C] {α : Type t} {A B : α → C}
    (g : ∀ a, A a ⟶ B a) (hg : ∀ a, d.I (g a))
    {X Y : C} {u : X ⟶ Y} (c : AttachCells.{w} g u) :
    ∃ (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty ((originalCells d).TransfiniteCompositionOfShape J u) := by
  obtain ⟨order, wf⟩ := exists_wellFoundedLT c.ι
  let _ : LinearOrder c.ι := order
  let _ : WellFoundedLT c.ι := wf
  let _ : SuccOrder (CoproductCells.cellOrder c.ι) := SuccOrder.ofLinearWellFoundedLT _
  exact ⟨CoproductCells.cellOrder c.ι, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨attachmentCoordinateChain d g hg c⟩⟩

/-- The original endpoint tests extend across every actual original
coproduct attachment, using its supplied cofan and pushout histories. -/
theorem originalAttachment_postcomp_weak [IsLeftProper C]
    {A B : C} {u : A ⟶ B} (c : AttachCells.{w} d.I.homFamily u)
    [IsCofibrant A] {X Y : C} (f : X ⟶ Y)
    (hTests : ∀ i : d.I.toSet,
      IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.left f) ∧
        IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.right f))
    (hA : WeakEquivalence (rawPostcomp d A f)) : WeakEquivalence (rawPostcomp d B f) := by
  let _ : HasCoproducts.{w} C := d.hasCoproducts
  obtain ⟨J, hJ, hBot, hSucc, hWF, ⟨history⟩⟩ :=
    attachmentHasOriginalCoordinateHistory d d.I.homFamily (fun i => i.2) c
  let _ : LinearOrder J := hJ
  let _ : OrderBot J := hBot
  let _ : SuccOrder J := hSucc
  let _ : WellFoundedLT J := hWF
  exact originalCell_chain_postcomp_weak d history f hTests hA

section OriginalRelativeCells

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- Full original I-cell complexes inherit the endpoint tests through
their original bottom, all original coproduct attachments and every
original continuous limit, with the supplied endpoint cocone retained. -/
theorem originalRelativeCell_postcomp_weak [IsLeftProper C]
    {A B : C} {u : A ⟶ B}
    (c : RelativeCellComplex.{w} (fun (_ : J) => d.I.homFamily) u)
    [IsCofibrant A] {X Y : C} (f : X ⟶ Y)
    (hTests : ∀ i : d.I.toSet,
      IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.left f) ∧
        IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.right f))
    (hA : WeakEquivalence (rawPostcomp d A f)) : WeakEquivalence (rawPostcomp d B f) := by
  let _ : c.F.IsWellOrderContinuous := c.isWellOrderContinuous
  let _ : (cofibrations C).IsStableUnderCoproducts.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let _ : Cofibration c.isoBot.inv := inferInstance
  let _ : IsCofibrant (c.F.obj ⊥) := isCofibrant_of_cofibration c.isoBot.inv
  let cc := c.transfiniteCompositionOfShape' (I := cofibrations C)
    (fun s => (cofibration_iff _).mp (original_I_cofibration d s.i))
  have hCF : (coproducts.{w} (cofibrations C)).pushouts ≤ cofibrations C :=
    (pushouts_monotone (cofibrations C).coproducts_le).trans (cofibrations C).pushouts_le
  have hF (j : J) (hj : ¬IsMax j) : Cofibration (c.F.map (homOfLE (Order.le_succ j))) :=
    (cofibration_iff _).mpr (hCF _ (cc.map_mem j hj))
  let _ : ∀ j : J, IsCofibrant (c.F.obj j) := fun j => continuous_source_obj_cofibrant d c.F hF j
  have hBot : WeakEquivalence (rawPostcomp d (c.F.obj ⊥) f) :=
    (nativePostcomp_iff_raw d _ f).mp
      ((nativePostcomp_weak_source_iff d c.isoBot.hom
        ((weakEquivalences C).of_isIso c.isoBot.hom) f).mpr ((nativePostcomp_iff_raw d A f).mpr hA))
  have hSucc (j : J) (hj : ¬IsMax j) (h : WeakEquivalence (rawPostcomp d (c.F.obj j) f)) :
      WeakEquivalence (rawPostcomp d (c.F.obj (Order.succ j)) f) :=
    originalAttachment_postcomp_weak d (c.attachCells j hj) f hTests h
  exact raw_continuous_postcomp_weak d c.F hF f (raw_continuous_pointwise d c.F hF f hBot hSucc)
    (Cocone.mk B c.incl) c.isColimit

end OriginalRelativeCells

/-- The entire original generated QA is the original fixed-κ I-cell
middle object at its original initial arrow. -/
theorem Q_original_cell_object (A : C) :
    let _ : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    (Q d).obj A = SmallObject.obj d.I κ (initial.to A) := by
  let _ : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  rw [Q_obj]
  exact d.cofibrantFactorizationData_obj (Arrow.mk (initial.to A))

/-- Hovey's original generating-endpoint detector, at arbitrary original
arrow endpoints. No generating endpoint is assumed cofibrant. The proof
uses the same original κ, Q, I-cell histories and native function complexes. -/
theorem weak_iff_original_I_endpoint_tests [IsLeftProper C] {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∀ i : d.I.toSet,
      IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.left f) ∧
        IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.right f) := by
  constructor
  · intro hf i
    have h := (weak_iff_native_postcomp_all d f).mp hf
    exact ⟨h i.1.left, h i.1.right⟩
  · intro hTests
    let _ : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    let _ : IsCofibrant (⊥_ C) :=
      (isCofibrant_iff_of_isInitial (𝟙 (⊥_ C)) initialIsInitial).mpr (by infer_instance)
    apply (weak_iff_native_postcomp_all d f).mpr
    intro A
    apply (nativePostcomp_iff_raw_Q d A f).mpr
    rw [Q_original_cell_object d A]
    exact originalRelativeCell_postcomp_weak d
      (SmallObject.relativeCellComplexιObj d.I κ (initial.to A)) f hTests (raw_initial_postcomp_weak d f)

/-- Both original generating families provide the same full original weak
detector. The original I/J endpoints and every generated QA remain unchanged. -/
theorem weak_iff_original_IJ_endpoint_tests [IsLeftProper C] {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔
      (∀ i : d.I.toSet,
        IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.left f) ∧
          IsIso (GeneratedRightMappingEnrichment.postcomp d i.1.right f)) ∧
      (∀ j : d.J.toSet,
        IsIso (GeneratedRightMappingEnrichment.postcomp d j.1.left f) ∧
          IsIso (GeneratedRightMappingEnrichment.postcomp d j.1.right f)) := by
  constructor
  · intro hf
    have h := (weak_iff_native_postcomp_all d f).mp hf
    exact ⟨fun i => ⟨h i.1.left, h i.1.right⟩, fun j => ⟨h j.1.left, h j.1.right⟩⟩
  · intro h
    exact (weak_iff_original_I_endpoint_tests d f).mpr h.1

end HomotopicalAlgebra.CellularGeneratingEndpointDetection
