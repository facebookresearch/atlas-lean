/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ISuspensionIntegerPi
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereNullHom
import MathlibExt.CategoryTheory.Enriched.ScalarTensor
import MathlibExt.CategoryTheory.Enriched.ScalarCotensor

/-!
# Original native (cofiber (I := I)) maps and integer scalar suspension

The original native projective replacement, (cone (I := I)) and chosen pushout remain
on the given enriched index. Restriction along the actual sequential
enriched index map calculates the original integer groups. Its scalar
tensor comparison is identity on every original level, and transports
the original signed sequential suspension isomorphism. No exactness or
sphere representation result is a caller parameter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v w z
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerMaps

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
  (integerStablePiLevelWeak_isIso)
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry
  (scalarLoopIntegerPiNatIso)
open PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry
  (piNPositive_isZero_subsingleton)

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

universe u₁ v₁ u₂ v₂ u₃ v₃

private def restrictedShiftIso {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] {G : Type u₃} [Category.{v₃} G]
    (U : D ⥤ E) (L : D ⥤ D) (T' : E ⥤ E) (P P' : E ⥤ G)
    (s : P ≅ T' ⋙ P') (rho : L ⋙ U ≅ U ⋙ T') :
    U ⋙ P ≅ L ⋙ (U ⋙ P') :=
  Functor.isoWhiskerLeft U s ≪≫ (Functor.associator U T' P').symm ≪≫
    Functor.isoWhiskerRight rho.symm P' ≪≫ Functor.associator L U P'

private theorem restrictedShiftIso_hom_app {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] {G : Type u₃} [Category.{v₃} G]
    (U : D ⥤ E) (L : D ⥤ D) (T' : E ⥤ E) (P P' : E ⥤ G)
    (s : P ≅ T' ⋙ P') (rho : L ⋙ U ≅ U ⋙ T') (X : D) :
    (restrictedShiftIso U L T' P P' s rho).hom.app X =
      s.hom.app (U.obj X) ≫ P'.map (rho.inv.app X) := by
  simp only [restrictedShiftIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp]

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
private abbrev N := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Restriction retains the original index actions and every whole input map. -/
abbrev underlyingSequential (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I) :
    (Carrier.{u, v} (I := I)) ⥤ PointedCGWH.SequentialSpectrum.{u, v} := restriction j

/-- Every native integer group is the unchanged underlying-prespectrum quotient group. -/
def integerPiFunctor (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I) (q : ℤ) :
    (Carrier.{u, v} (I := I)) ⥤ GrpCat.{v} := underlyingSequential j ⋙ integerStablePiFunctor q

/-- The full changing-degree diagram has the original positive tail and all transition maps. -/
def integerDiagonalFunctor (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I) (q : ℤ) :
    (Carrier.{u, v} (I := I)) ⥤ (ℕ ⥤ GrpCat.{v}) :=
  underlyingSequential j ⋙ integerDiagonalDiagramFunctor q

/-- The original level index after the actual sequential embedding. -/
def sourceIndex (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I) (m : ℕ) : I :=
  j.obj (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)

/-- Every original native coefficient level is retained literally. -/
theorem underlying_level (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I)
    (X : (Carrier.{u, v} (I := I))) (m : ℕ) :
    ((underlyingSequential j).obj X).level m = X.toEnrichedFunctor.obj (sourceIndex j m) := rfl

/-- Every complete original transformation retains its original component at that level. -/
theorem underlying_map (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I)
    {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap ((underlyingSequential j).map f) m =
      component f (sourceIndex j m) :=
  restrictionMap_component j f
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)

/-- Every native stage map is the original positive homotopy map of that same component. -/
theorem integerDiagonalFunctor_map_stage
    (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I) (q : ℤ)
    {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (n : ℕ) :
    ((integerDiagonalFunctor j q).map f).app n =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (component f (sourceIndex j (integerTailLevel q + n))) :=
  congrArg ((PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map)
    (underlying_map j f (integerTailLevel q + n))

/-- The actual native group leg is the unchanged positive-tail quotient leg. -/
def integerPiLeg (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I)
    (q : ℤ) (X : (Carrier.{u, v} (I := I))) (n : ℕ) :
    (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).obj
      (X.toEnrichedFunctor.obj (sourceIndex j (integerTailLevel q + n))) ⟶
        (integerPiFunctor j q).obj X :=
  integerStablePiLeg q ((underlyingSequential j).obj X) n

/-- Both original endpoints and the complete evaluated input map remain on the same quotient leg. -/
theorem integerPiLeg_naturality_component
    (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I) (q : ℤ)
    {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (n : ℕ) :
    integerPiLeg j q X n ≫ (integerPiFunctor j q).map f =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (component f (sourceIndex j (integerTailLevel q + n))) ≫ integerPiLeg j q Y n := by
  have h := integerStablePiLeg_naturality q ((underlyingSequential j).map f) n
  have hm := underlying_map j f (integerTailLevel q + n)
  change PointedCGWH.SequentialSpectrum.levelMap (restrictionMap j f)
    (integerTailLevel q + n) = component f (sourceIndex j (integerTailLevel q + n)) at hm
  simpa only [integerPiLeg, integerPiFunctor, Functor.comp_map, hm] using h

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  HomotopicalAlgebra.EnrichedProjective.Native.Replacement.isCofibrant_cofibrantReplacement

private abbrev Index := I
private abbrev H := toHomotopyCategory (Carrier.{u, v} (I := I))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)
private abbrev cone := OriginalICone.cone (B := B) (I := I)
private abbrev ι := OriginalICone.inclusion (B := B) (I := I)
private abbrev c := OriginalISuspension.cocone (B := B) (I := I)
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := I)
private abbrev suspensionCocone (X : (Carrier.{u, v} (I := I))) := c (Arrow.mk (Diagrams.toZero X))
private abbrev T := tensorLeft (A := I) PointedCGWH.sphereOne.{u, v}
private abbrev R := cotensor (I := I) PointedCGWH.sphereOne.{u, v}
private abbrev TSeq :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionGeometry.suspension.{u, v}
private abbrev RSeq := PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionGeometry.loop.{u, v}
private abbrev scalarAdj := ScalarLeibniz.adjunction (A := I) PointedCGWH.sphereOne.{u, v}

variable {j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I}

/-- Restriction takes every original level weak map to the same underlying level weak map. -/
theorem underlying_levelWeak {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} (I := I)) f) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((underlyingSequential j).map f) := by
  rw [Native.weakEquivalences_eq, EvaluationTransfer.evaluationProperty_iff] at hf ⊢
  intro a
  change weakEquivalences PointedCGWH.{u, v} (component (restrictionMap j f) a)
  rw [restrictionMap_component]
  exact hf (j.obj a)

/-- The actual native integer functor inverts the original level weak maps. -/
theorem integerPiFunctor_invertsLevelWeak (q : ℤ) :
    (weakEquivalences (Carrier.{u, v} (I := I))).IsInvertedBy (integerPiFunctor j q) :=
  fun _ _ f hf =>
    integerStablePiLevelWeak_isIso q ((underlyingSequential j).map f)
        (underlying_levelWeak (j := j) f hf)

/-- Both maps of the integer comparison are the original native level-weak map and its inverse. -/
def integerPiLevelWeakIso (q : ℤ) {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} (I := I)) f) :
    (integerPiFunctor j q).obj X ≅ (integerPiFunctor j q).obj Y :=
  @asIso _ _ _ _ ((integerPiFunctor j q).map f) (integerPiFunctor_invertsLevelWeak (j := j) q f hf)

/-- The full forward weak-comparison map is the unchanged original native quotient map. -/
theorem integerPiLevelWeakIso_hom (q : ℤ) {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} (I := I)) f) :
    (integerPiLevelWeakIso (j := j) q f hf).hom = (integerPiFunctor j q).map f := rfl

/-- The same original integer maps descend through the actual native level localization. -/
def integerPiHoFunctor (j : EnrichedFunctor PointedCGWH.{u, v} N.{u, v} I) (q : ℤ) :
    HomotopyCategory (Carrier.{u, v} (I := I)) ⥤ GrpCat.{v} :=
  Localization.Construction.lift (integerPiFunctor j q) (integerPiFunctor_invertsLevelWeak (j :=
    j) q)

/-- Every original represented object keeps exactly its original integer group. -/
theorem integerPiHoFunctor_obj (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (integerPiHoFunctor j q).obj ((H (I := I)).obj X) = (integerPiFunctor j q).obj X := rfl

/-- The exact represented native group object keeps its original identity comparison. -/
def integerPiHoObjectIso (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (integerPiHoFunctor j q).obj ((H (I := I)).obj X) ≅ (integerPiFunctor j q).obj X :=
  eqToIso (integerPiHoFunctor_obj (j := j) q X)

/-- Full Ho isomorphisms act on the same original native groups through their identity
comparisons. -/
def integerPiHoIso (q : ℤ) {X Y : (Carrier.{u, v} (I := I))}
    (e : (H (I := I)).obj X ≅ (H (I := I)).obj Y) :
    (integerPiFunctor j q).obj X ≅ (integerPiFunctor j q).obj Y :=
  (integerPiHoObjectIso (j := j) q X).symm ≪≫
    (integerPiHoFunctor j q).mapIso e ≪≫ integerPiHoObjectIso (j := j) q Y

/-- The native-group Ho isomorphism keeps the original full Ho map. -/
theorem integerPiHoIso_hom (q : ℤ) {X Y : (Carrier.{u, v} (I := I))}
    (e : (H (I := I)).obj X ≅ (H (I := I)).obj Y) :
    (integerPiHoIso (j := j) q e).hom = (integerPiHoFunctor j q).map e.hom := by
  change (𝟙 _ ≫ (integerPiHoFunctor j q).map e.hom) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- The full descended functor retains the unchanged original group functor and all maps. -/
theorem integerPiHoFunctor_original (q : ℤ) :
    (H (I := I)) ⋙ integerPiHoFunctor j q = integerPiFunctor j q :=
  Localization.Construction.fac (integerPiFunctor j q) (integerPiFunctor_invertsLevelWeak (j := j)
    q)

/-- Every represented map is the original quotient-group map of the same native input. -/
theorem integerPiHoFunctor_map (q : ℤ) {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) :
    (integerPiHoFunctor j q).map ((H (I := I)).map f) = (integerPiFunctor j q).map f := by
  have h := Functor.congr_hom (integerPiHoFunctor_original (j := j) q) f
  change (integerPiHoFunctor j q).map ((H (I := I)).map f) =
    𝟙 _ ≫ (integerPiFunctor j q).map f ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

private instance nativeZero : HasZeroObject (Carrier.{u, v} (I := I)) :=
  Diagrams.nativeHasZeroObject

/-- The same original chosen Q cofiber is kept on every complete source arrow. -/
abbrev cofiber : Arrow (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I)) :=
  CofiberNullity.cofiberQ (B := B)

/-- The actual target inclusion of the original chosen whole-arrow Q cofiber. -/
def inclusion (F : Arrow (Carrier.{u, v} (I := I))) :
    (Q (I := I)).obj F.right ⟶ (cofiber (I := I)).obj F :=
  (OriginalISuspension.cocone (B := B) ((Q (I := I)).mapArrow.obj F)).inr

/-- The full target inclusion is natural on the original two-component arrow square. -/
theorem inclusion_naturality {F G : Arrow (Carrier.{u, v} (I := I))}
    (q : F ⟶ G) :
    (Q (I := I)).map q.right ≫ inclusion G = inclusion F ≫ (cofiber (I := I)).map q := by
  exact (OrdinaryHoChosenPuppe.cofiberMap_target
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B))
    (OriginalISuspension.coconeIsColimit (B := B)) ((Q (I := I)).mapArrow.map q)).symm

/-- The original level-weak Q counit has its actual image isomorphism. -/
def qCounitHoIso (X : (Carrier.{u, v} (I := I))) : (H (I := I)).obj ((Q (I := I)).obj X) ≅ (H (I
  := I)).obj X :=
  Localization.Construction.wIso ((ε (I := I)).app X)
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B) X).2

/-- The source target-to-cofiber arrow keeps the original Q inverse and actual chosen inclusion. -/
def inclusionHo (F : Arrow (Carrier.{u, v} (I := I))) :
    (H (I := I)).obj F.right ⟶ (H (I := I)).obj ((cofiber (I := I)).obj F) :=
  (qCounitHoIso F.right).inv ≫ (H (I := I)).map (inclusion F)

/-- Every integer degree retains the exact original Q/inclusion group map. -/
def inclusionInteger (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (integerPiHoFunctor j q).obj ((H (I := I)).obj F.right) ⟶
      (integerPiHoFunctor j q).obj ((H (I := I)).obj ((cofiber (I := I)).obj F)) :=
  (integerPiHoFunctor j q).map (inclusionHo F)

/-- The full cofiber group map is the original quotient map of the Q comparison and inclusion. -/
theorem inclusionInteger_formula (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    inclusionInteger (j := j) q F =
      (integerPiHoFunctor j q).map (qCounitHoIso F.right).inv ≫
        (integerPiFunctor j q).map (inclusion F) := by
  rw [inclusionInteger, inclusionHo, Functor.map_comp, integerPiHoFunctor_map (j := j)]

/-- The unchanged counit retains its whole original input-map square. -/
theorem qCounitHoIso_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) :
    (H (I := I)).map ((Q (I := I)).map f) ≫ (qCounitHoIso Y).hom = (qCounitHoIso X).hom ≫ (H (I :=
      I)).map f :=
  ((H (I := I)).map_comp _ _).symm.trans (((H (I := I)).congr_map ((ε (I := I)).naturality
    f)).trans ((H (I := I)).map_comp _ _))

/-- Both full inverse counit functions retain the original input map. -/
theorem qCounitHoIso_inverse_naturality {X Y : (Carrier.{u, v} (I := I))}
    (f : X ⟶ Y) :
    (H (I := I)).map f ≫ (qCounitHoIso Y).inv = (qCounitHoIso X).inv ≫ (H (I := I)).map ((Q (I :=
      I)).map f) := by
  apply (cancel_epi (qCounitHoIso X).hom).mp
  calc
    (qCounitHoIso X).hom ≫ ((H (I := I)).map f ≫ (qCounitHoIso Y).inv) =
        (H (I := I)).map ((Q (I := I)).map f) ≫ ((qCounitHoIso Y).hom ≫ (qCounitHoIso Y).inv) := by
      rw [← Category.assoc, ← qCounitHoIso_naturality f, Category.assoc]
    _ = (H (I := I)).map ((Q (I := I)).map f) := by rw [Iso.hom_inv_id, Category.comp_id]
    _ = (qCounitHoIso X).hom ≫ ((qCounitHoIso X).inv ≫ (H (I := I)).map ((Q (I := I)).map f)) := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The original whole-arrow target function acts naturally on the actual cofiber inclusion. -/
theorem inclusionHo_naturality {F G : Arrow (Carrier.{u, v} (I := I))}
    (m : F ⟶ G) :
    (H (I := I)).map m.right ≫ inclusionHo G = inclusionHo F ≫ (H (I := I)).map ((cofiber (I :=
      I)).map m) := by
  rw [inclusionHo, inclusionHo, ← Category.assoc, qCounitHoIso_inverse_naturality,
    Category.assoc, ← (H (I := I)).map_comp, inclusion_naturality,
    (H (I := I)).map_comp, ← Category.assoc]

/-- Every integer quotient map retains both full original Arrow target maps. -/
theorem inclusionInteger_naturality (q : ℤ)
    {F G : Arrow (Carrier.{u, v} (I := I))} (m : F ⟶ G) :
    (integerPiFunctor j q).map m.right ≫ inclusionInteger (j := j) q G =
      inclusionInteger (j := j) q F ≫ (integerPiFunctor j q).map ((cofiber (I := I)).map m) := by
  have h := (integerPiHoFunctor j q).congr_map (inclusionHo_naturality m)
  simp only [Functor.map_comp, integerPiHoFunctor_map (j := j)] at h
  exact h

/-- The original Q cofiber boundary retains its actual chosen suspension target. -/
def boundary (F : Arrow (Carrier.{u, v} (I := I))) :
    (cofiber (I := I)).obj F ⟶ (OriginalISuspension.suspension (B := B)).obj ((Q (I := I)).obj
      F.left) :=
  OrdinaryHoChosenPuppe.boundary
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.obj F)

/-- Every entire Q arrow retains the original cofiber-boundary square. -/
theorem boundary_naturality {F G : Arrow (Carrier.{u, v} (I := I))}
    (m : F ⟶ G) :
    (cofiber (I := I)).map m ≫ boundary G = boundary F ≫
      (OriginalISuspension.suspension (B := B)).map ((Q (I := I)).map m.left) :=
  OrdinaryHoChosenPuppe.boundary_naturality
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.map m)

/-- The boundary's full cone leg is the unchanged original suspension cone leg. -/
theorem boundary_cone (F : Arrow (Carrier.{u, v} (I := I))) :
    (OriginalISuspension.cocone (B := B) ((Q (I := I)).mapArrow.obj F)).inl ≫ boundary F =
      (OriginalISuspension.cocone (B := B)
        (Arrow.mk (Diagrams.toZero ((Q (I := I)).obj F.left)))).inl :=
  OrdinaryHoChosenPuppe.boundary_cone
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.obj F)

/-- The complete target leg of the boundary factors through the original native zero. -/
theorem inclusion_boundary (F : Arrow (Carrier.{u, v} (I := I))) :
    inclusion F ≫ boundary F = Diagrams.toZero ((Q (I := I)).obj F.right) ≫
      (OriginalISuspension.cocone (B := B)
        (Arrow.mk (Diagrams.toZero ((Q (I := I)).obj F.left)))).inr :=
  OrdinaryHoChosenPuppe.boundary_target
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.obj F)

/-- Original classes of every independent native family retain both identity-component maps. -/
def projectedIntegerClassNatIso {A : Type w} [Category.{z} A]
    (F : A ⥤ (Carrier.{u, v} (I := I))) (q : ℤ) :
    (F ⋙ (H (I := I))) ⋙ integerPiHoFunctor j q ≅ F ⋙ integerPiFunctor j q :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change (integerPiHoFunctor j q).map ((H (I := I)).map (F.map f)) ≫ 𝟙 _ =
      𝟙 _ ≫ (integerPiFunctor j q).map (F.map f)
    rw [Category.comp_id, Category.id_comp, integerPiHoFunctor_map (j := j)])

/-- The projected group's forward class function is the exact quotient identity. -/
theorem projectedIntegerClassNatIso_hom_app {A : Type w} [Category.{z} A]
    (F : A ⥤ (Carrier.{u, v} (I := I))) (q : ℤ) (X : A) :
    (projectedIntegerClassNatIso (j := j) F q).hom.app X =
      𝟙 ((integerPiFunctor j q).obj (F.obj X)) := rfl

/-- The inverse projected class function is the same original quotient identity. -/
theorem projectedIntegerClassNatIso_inv_app {A : Type w} [Category.{z} A]
    (F : A ⥤ (Carrier.{u, v} (I := I))) (q : ℤ) (X : A) :
    (projectedIntegerClassNatIso (j := j) F q).inv.app X =
      𝟙 ((integerPiFunctor j q).obj (F.obj X)) := rfl

/-- Both scalar tensor restriction maps retain identity components at every original level. -/
def suspensionRestrictionNatIso :
    tensorLeft (A := I) PointedCGWH.sphereOne.{u, v} ⋙ underlyingSequential j ≅
      underlyingSequential j ⋙
        PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionGeometry.suspension.{u, v} :=
  (NatIso.ofComponents
    (fun X => tensorLeftRestrictionIso PointedCGWH.sphereOne j X)
    (fun f => tensorLeftRestrictionIso_naturality PointedCGWH.sphereOne j f)).symm

/-- The full inverse restriction component has its exact original tensor endpoints. -/
def suspensionRestrictionInv (X : (Carrier.{u, v} (I := I))) :
    TSeq.obj ((underlyingSequential j).obj X) ⟶
      (underlyingSequential j).obj ((T (I := I)).obj X) :=
  (suspensionRestrictionNatIso (j := j)).inv.app X

/-- The original signed scalar suspension comparison is transported through the same tensor maps. -/
def scalarIntegerPiNatIso (q : ℤ) : integerPiFunctor j q ≅
    tensorLeft (A := I) PointedCGWH.sphereOne.{u, v} ⋙ integerPiFunctor j (q + 1) :=
  restrictedShiftIso (underlyingSequential j) (T (I := I)) TSeq
    (integerStablePiFunctor q) (integerStablePiFunctor (q + 1))
    (integerSuspensionPiNatIso q) (suspensionRestrictionNatIso (j := j))

omit B in
/-- The entire forward scalar map is the actual sequential unit class followed by restriction. -/
theorem scalarIntegerPiNatIso_hom_app (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (scalarIntegerPiNatIso (j := j) q).hom.app X =
      @CategoryStruct.comp GrpCat.{v} inferInstance
        ((integerPiFunctor j q).obj X)
        ((integerStablePiFunctor (q + 1)).obj (TSeq.obj ((underlyingSequential j).obj X)))
        ((integerPiFunctor j (q + 1)).obj ((T (I := I)).obj X))
        ((integerSuspensionPiNatIso q).hom.app ((underlyingSequential j).obj X))
        ((integerStablePiFunctor (q + 1)).map (suspensionRestrictionInv (j := j) X)) := by
  exact restrictedShiftIso_hom_app (underlyingSequential j) (T (I := I)) TSeq
    (integerStablePiFunctor q) (integerStablePiFunctor (q + 1))
    (integerSuspensionPiNatIso q) (suspensionRestrictionNatIso (j := j)) X


/-- The actual scalar cotensor restriction retains both original identity-component maps. -/
def loopRestrictionNatIso : (R (I := I)) ⋙ underlyingSequential j ≅ underlyingSequential j ⋙ RSeq :=
  NatIso.ofComponents
    (fun X => (cotensorRestrictionIso j PointedCGWH.sphereOne X).symm)
    (fun {X Y} f => by
      apply (cotensorRestrictionIso j PointedCGWH.sphereOne Y).comp_inv_eq.mpr
      exact ((cotensorRestrictionIso j PointedCGWH.sphereOne X).inv_comp_eq.mpr
        (cotensorRestrictionIso_naturality j PointedCGWH.sphereOne f)).symm.trans
          (Category.assoc _ _ _).symm)

/-- Every integer native loop class uses the same original signed sequential quotient comparison. -/
def nativeScalarLoopPiNatIso (q : ℤ) : (R (I := I)) ⋙ integerPiFunctor j q ≅ integerPiFunctor j (q
  + 1) :=
  (Functor.associator (R (I := I)) (underlyingSequential j) (integerStablePiFunctor q)).symm ≪≫
    Functor.isoWhiskerRight (loopRestrictionNatIso (j := j)) (integerStablePiFunctor q) ≪≫
    Functor.associator (underlyingSequential j) RSeq (integerStablePiFunctor q) ≪≫
    Functor.isoWhiskerLeft (underlyingSequential j)
      (scalarLoopIntegerPiNatIso q)

omit B in
/-- Its forward component is the actual cotensor restriction map
before the same signed class map. -/
theorem nativeScalarLoopPiNatIso_hom_app (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (nativeScalarLoopPiNatIso (j := j) q).hom.app X =
      (integerStablePiFunctor q).map ((loopRestrictionNatIso (j := j)).hom.app X) ≫
        (scalarLoopIntegerPiNatIso q).hom.app ((underlyingSequential j).obj X) := by
  simp only [nativeScalarLoopPiNatIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp]
  exact Category.id_comp _

omit B in
private theorem scalarUnit_component {J : Type} [EnrichedCategory PointedCGWH.{u, v} J]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} J) (a : J) :
    component ((ScalarLeibniz.adjunction PointedCGWH.sphereOne).unit.app X) a =
      MonoidalClosed.curry (𝟙 (PointedCGWH.sphereOne ⊗ X.toEnrichedFunctor.obj a)) := by
  change component (ScalarLeibniz.adjunct PointedCGWH.sphereOne X _ (𝟙 _)) a = _
  rw [ScalarLeibniz.adjunct_component]
  exact congrArg MonoidalClosed.curry (component_id _ a)

omit B in
/-- The actual native scalar unit preserves both full restriction comparisons before the original
unit. -/
theorem scalarUnit_restriction (X : (Carrier.{u, v} (I := I))) :
    (underlyingSequential j).map ((scalarAdj (I := I)).unit.app X) ≫
        ((loopRestrictionNatIso (j := j)).hom.app ((T (I := I)).obj X)) ≫
        RSeq.map ((suspensionRestrictionNatIso (j := j)).hom.app X) =
      PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionGeometry.unit.app
        ((underlyingSequential j).obj X) := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  let b := j.obj a
  let η := MonoidalClosed.curry (𝟙 (PointedCGWH.sphereOne ⊗ X.toEnrichedFunctor.obj b))
  have hU : component ((underlyingSequential j).map ((scalarAdj (I := I)).unit.app X)) a = η :=
    (restrictionMap_component j ((scalarAdj (I := I)).unit.app X) a).trans (scalarUnit_component X
      b)
  have hR : component (((loopRestrictionNatIso (j := j)).hom.app ((T (I := I)).obj X))) a =
      𝟙 (PointedCGWH.loop.obj (PointedCGWH.sphereOne ⊗ X.toEnrichedFunctor.obj b)) :=
    cotensorRestrictionIso_inv_component j PointedCGWH.sphereOne ((T (I := I)).obj X) a
  have hT : component (((suspensionRestrictionNatIso (j := j)).hom.app X)) a =
      𝟙 (PointedCGWH.sphereOne ⊗ X.toEnrichedFunctor.obj b) :=
    tensorLeftRestrictionIso_inv_component PointedCGWH.sphereOne j X a
  have hRT : component (RSeq.map ((suspensionRestrictionNatIso (j := j)).hom.app X)) a =
      𝟙 (PointedCGWH.loop.obj (PointedCGWH.sphereOne ⊗ X.toEnrichedFunctor.obj b)) :=
    (cotensorMap_component PointedCGWH.sphereOne
      ((suspensionRestrictionNatIso (j := j)).hom.app X) a).trans
      ((congrArg (PointedCGWH.loop.map) hT).trans (PointedCGWH.loop.map_id _))
  have hSeq := scalarUnit_component ((underlyingSequential j).obj X) a
  have hL := component_comp ((underlyingSequential j).map ((scalarAdj (I := I)).unit.app X))
    (((loopRestrictionNatIso (j := j)).hom.app ((T (I := I)).obj X)) ≫
      RSeq.map ((suspensionRestrictionNatIso (j := j)).hom.app X)) a
  have hInner := component_comp (((loopRestrictionNatIso (j := j)).hom.app ((T (I := I)).obj X)))
    (RSeq.map ((suspensionRestrictionNatIso (j := j)).hom.app X)) a
  have hInnerId : component (((loopRestrictionNatIso (j := j)).hom.app ((T (I := I)).obj X)) ≫
      RSeq.map ((suspensionRestrictionNatIso (j := j)).hom.app X)) a = 𝟙 _ :=
    hInner.trans ((congrArg₂ (fun f g => f ≫ g) hR hRT).trans (Category.id_comp _))
  exact hL.trans ((congrArg₂ (fun f g => f ≫ g) hU hInnerId).trans
    ((Category.comp_id η).trans hSeq.symm))

omit B in
/-- The full native scalar suspension class map is the actual native unit before the signed loop
map. -/
theorem scalarIntegerPiNatIso_hom_native_unit (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (scalarIntegerPiNatIso (j := j) q).hom.app X =
      (integerPiFunctor j q).map ((scalarAdj (I := I)).unit.app X) ≫
        (nativeScalarLoopPiNatIso (j := j) q).hom.app ((T (I := I)).obj X) := by
  let e := (suspensionRestrictionNatIso (j := j)).app X
  let t := (integerStablePiFunctor (q + 1)).map e.hom
  let _ : IsIso t := inferInstance
  apply (cancel_mono t).mp
  have hLeft : (scalarIntegerPiNatIso (j := j) q).hom.app X ≫ t =
      (integerSuspensionPiNatIso q).hom.app ((underlyingSequential j).obj X) := by
    rw [scalarIntegerPiNatIso_hom_app (j := j)]
    change (_ ≫ (integerStablePiFunctor (q + 1)).map e.inv) ≫
      (integerStablePiFunctor (q + 1)).map e.hom = _
    rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hUnit := (integerStablePiFunctor q).congr_map (scalarUnit_restriction (j := j) X)
  simp only [Functor.map_comp] at hUnit
  let l := scalarLoopIntegerPiNatIso q
  have hn := l.hom.naturality e.hom
  have hn' := hn.symm
  have hRight : ((integerPiFunctor j q).map ((scalarAdj (I := I)).unit.app X) ≫
      (nativeScalarLoopPiNatIso (j := j) q).hom.app ((T (I := I)).obj X)) ≫ t =
        (integerSuspensionPiNatIso q).hom.app ((underlyingSequential j).obj X) := by
    rw [nativeScalarLoopPiNatIso_hom_app (j := j)]
    change ((integerStablePiFunctor q).map ((underlyingSequential j).map ((scalarAdj (I :=
      I)).unit.app X)) ≫
      ((integerStablePiFunctor q).map ((loopRestrictionNatIso (j := j)).hom.app ((T (I := I)).obj
        X)) ≫
        l.hom.app ((underlyingSequential j).obj ((T (I := I)).obj X)))) ≫ t = _
    calc
      _ = (integerStablePiFunctor q).map ((underlyingSequential j).map ((scalarAdj (I :=
        I)).unit.app X)) ≫
          (integerStablePiFunctor q).map ((loopRestrictionNatIso (j := j)).hom.app ((T (I :=
            I)).obj X)) ≫
          (l.hom.app ((underlyingSequential j).obj ((T (I := I)).obj X)) ≫ t) := by
            simp only [Category.assoc]
      _ = ((integerStablePiFunctor q).map ((underlyingSequential j).map ((scalarAdj (I :=
        I)).unit.app X)) ≫
          (integerStablePiFunctor q).map ((loopRestrictionNatIso (j := j)).hom.app ((T (I :=
            I)).obj X)) ≫
          (integerStablePiFunctor q).map (RSeq.map e.hom)) ≫
          l.hom.app (TSeq.obj ((underlyingSequential j).obj X)) := by
            change l.hom.app ((underlyingSequential j).obj ((T (I := I)).obj X)) ≫ t =
              (integerStablePiFunctor q).map (RSeq.map e.hom) ≫
                l.hom.app (TSeq.obj ((underlyingSequential j).obj X)) at hn'
            rw [hn']
            simp only [Category.assoc]
      _ = (integerStablePiFunctor q).map
          (PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionGeometry.unit.app
            ((underlyingSequential j).obj X)) ≫
          l.hom.app (TSeq.obj ((underlyingSequential j).obj X)) :=
        congrArg (fun z => z ≫ l.hom.app (TSeq.obj ((underlyingSequential j).obj X))) hUnit
      _ = _ := ((integerSuspensionPiNatIso_hom_app q ((underlyingSequential j).obj X)).trans
        (integerSuspensionPiMap_app q ((underlyingSequential j).obj X))).symm
  exact hLeft.trans hRight.symm

private abbrev cι : CofibrantObject (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I)) :=
  CofibrantObject.ι

/-- Both whole cofibrant source functors retain the original I/scalar Ho comparison. -/
def cofibrantIScalarHoNatIso : (cι (I := I) ⋙ (S (I := I))) ⋙ (H (I := I)) ≅
    (cι (I := I) ⋙ (T (I := I))) ⋙ (H (I := I)) :=
  Functor.associator (cι (I := I)) (S (I := I)) (H (I := I)) ≪≫
    OriginalISuspensionCofibrantComparison.cofibrantNatIso (B := B) (I := I) ≪≫
    (Functor.associator (cι (I := I)) (T (I := I)) (H (I := I))).symm

/-- The full cofibrant integer comparison retains every original map before component evaluation. -/
def cofibrantISuspensionPiNatIso (q : ℤ) :
    cι (I := I) ⋙ integerPiFunctor j q ≅
      cι (I := I) ⋙ ((S (I := I)) ⋙ integerPiFunctor j (q + 1)) :=
  Functor.isoWhiskerLeft (cι (I := I)) (scalarIntegerPiNatIso (j := j) q) ≪≫
    (Functor.associator (cι (I := I)) (T (I := I)) (integerPiFunctor j (q + 1))).symm ≪≫
    (projectedIntegerClassNatIso (j := j) (cι (I := I) ⋙ (T (I := I))) (q + 1)).symm ≪≫
    Functor.isoWhiskerRight (cofibrantIScalarHoNatIso (B := B) (I := I)).symm
      (integerPiHoFunctor j (q + 1)) ≪≫
    projectedIntegerClassNatIso (j := j) (cι (I := I) ⋙ (S (I := I))) (q + 1) ≪≫
    Functor.associator (cι (I := I)) (S (I := I)) (integerPiFunctor j (q + 1))

/-- Cofibrant I suspension uses the component of the same original whole comparison. -/
def cofibrantISuspensionPiIso (q : ℤ) (X : (Carrier.{u, v} (I := I))) [IsCofibrant X] :
    (integerPiFunctor j q).obj X ≅ (integerPiFunctor j (q + 1)).obj ((S (I := I)).obj X) :=
  (cofibrantISuspensionPiNatIso (j := j) q).app (CofibrantObject.mk X)

/-- All native cofibrant maps retain the same exact scalar/I-suspension square. -/
theorem cofibrantISuspensionPiIso_hom_naturality (q : ℤ)
    {X Y : (Carrier.{u, v} (I := I))} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    (integerPiFunctor j q).map f ≫ (cofibrantISuspensionPiIso (j := j) q Y).hom =
      (cofibrantISuspensionPiIso (j := j) q X).hom ≫
        (integerPiFunctor j (q + 1)).map ((S (I := I)).map f) :=
  (cofibrantISuspensionPiNatIso (j := j) q).hom.naturality (CofibrantObject.homMk f)

/-- The actual original Q counit is invertible on every original quotient group. -/
def qCounitIntegerNatIso (q : ℤ) : (Q (I := I)) ⋙ integerPiFunctor j q ≅ integerPiFunctor j q := by
  let α := Functor.whiskerRight (ε (I := I)) (integerPiFunctor j q)
  let _ : ∀ X, IsIso (α.app X) := fun X => integerPiFunctor_invertsLevelWeak (j := j) q
    ((ε (I := I)).app X) (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  let _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The original Q counit's forward group map is unchanged. -/
theorem qCounitIntegerNatIso_hom_app (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (qCounitIntegerNatIso (j := j) q).hom.app X =
      (integerPiFunctor j q).map ((ε (I := I)).app X) := rfl

/-- The I-Q comparison uses the original replacement and original I suspension. -/
abbrev originalISuspensionQFunctor : (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I)) := (Q
  (I := I)) ⋙ (S (I := I))

/-- The full original I-Q comparison is the Q inverse, scalar unit and same cone comparison. -/
def integerISuspensionPiNatIso (q : ℤ) : integerPiFunctor j q ≅
    (originalISuspensionQFunctor (I := I)) ⋙ integerPiFunctor j (q + 1) := by
  let _ : ∀ X : (Carrier.{u, v} (I := I)), IsCofibrant ((Q (I := I)).obj X) :=
    fun X => Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
  exact (qCounitIntegerNatIso (j := j) q).symm ≪≫
    NatIso.ofComponents (fun X => cofibrantISuspensionPiIso (j := j) q ((Q (I := I)).obj X))
      (fun f => cofibrantISuspensionPiIso_hom_naturality (j := j) q ((Q (I := I)).map f))

/-- The full I-Q word keeps the original Q inverse and the original cofibrant scalar comparison. -/
theorem integerISuspensionPiNatIso_hom_word (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (integerISuspensionPiNatIso (j := j) q).hom.app X =
      @CategoryStruct.comp GrpCat.{v} inferInstance
        ((integerPiFunctor j q).obj X)
        ((integerPiFunctor j q).obj ((Q (I := I)).obj X))
        ((integerPiFunctor j (q + 1)).obj ((S (I := I)).obj ((Q (I := I)).obj X)))
        ((qCounitIntegerNatIso (j := j) q).inv.app X)
        (cofibrantISuspensionPiIso (j := j) q ((Q (I := I)).obj X)).hom := by
  let _ : IsCofibrant ((Q (I := I)).obj X) :=
    Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
  rfl

/-- The complete inverse suspension function retains every unchanged original input map. -/
theorem integerISuspensionPiNatIso_inv_naturality (q : ℤ)
    {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) :
    @CategoryStruct.comp GrpCat.{v} inferInstance
      (((originalISuspensionQFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)).obj X)
      (((originalISuspensionQFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)).obj Y)
      ((integerPiFunctor j q).obj Y)
      (((originalISuspensionQFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)).map f)
      ((integerISuspensionPiNatIso (j := j) q).inv.app Y) =
    @CategoryStruct.comp GrpCat.{v} inferInstance
      (((originalISuspensionQFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)).obj X)
      ((integerPiFunctor j q).obj X) ((integerPiFunctor j q).obj Y)
      ((integerISuspensionPiNatIso (j := j) q).inv.app X) ((integerPiFunctor j q).map f) :=
  (integerISuspensionPiNatIso (j := j) q).inv.naturality f


omit B in
/-- Every original native zero stage is the unique pointed homotopy class. -/
theorem integerZero_stage_subsingleton (q : ℤ) (n : ℕ) :
    Subsingleton (((integerDiagonalFunctor j q).obj
      (Diagrams.zeroDiagram (A := I))).obj n) :=
  piNPositive_isZero_subsingleton (integerTailPositiveIndex q + n) _
      (Diagrams.initialDiagram_component_isZero
        (sourceIndex j (integerTailLevel q + n)))

omit B in
/-- Every original native zero quotient class is the unchanged group identity. -/
theorem integerZero_eq_one (q : ℤ)
    (a : (integerPiFunctor j q).obj (Diagrams.zeroDiagram (A := I))) : a = 1 := by
  let D := (integerDiagonalFunctor j q).obj (Diagrams.zeroDiagram (A := I))
  refine Quot.inductionOn a ?_
  intro x
  obtain ⟨n, b⟩ := x
  let _ := integerZero_stage_subsingleton (j := j) q n
  let b' : D.obj n := b
  have hb : b' = 1 := Subsingleton.elim _ _
  change GrpCat.FilteredColimits.G.mk D ⟨n, b'⟩ = 1
  rw [hb]
  exact (GrpCat.FilteredColimits.colimit_one_eq D n).symm

omit B in
/-- The original native zero has a trivial original group in every integer degree. -/
theorem integerZero_subsingleton (q : ℤ) :
    Subsingleton ((integerPiFunctor j q).obj (Diagrams.zeroDiagram (A := I))) :=
  ⟨fun a b => (integerZero_eq_one (j := j) q a).trans (integerZero_eq_one (j := j) q b).symm⟩

omit B in
/-- All maps factoring through the same actual native zero induce the trivial integer map. -/
theorem integerMap_through_zero_apply (q : ℤ) {X Y : (Carrier.{u, v} (I := I))}
    (f : X ⟶ Diagrams.zeroDiagram) (g : Diagrams.zeroDiagram ⟶ Y)
    (a : (integerPiFunctor j q).obj X) :
    ((integerPiFunctor j q).map (f ≫ g)).hom a = 1 := by
  rw [Functor.map_comp]
  change ((integerPiFunctor j q).map g).hom
    (((integerPiFunctor j q).map f).hom a) = 1
  rw [integerZero_eq_one (j := j) q (((integerPiFunctor j q).map f).hom a)]
  exact map_one _

omit B in
/-- The actual original native null map has its original trivial integer-class function. -/
theorem integerNullMap_apply (q : ℤ) (X Y : (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j q).obj X) :
    ((integerPiFunctor j q).map (Diagrams.toZero X ≫ Diagrams.zeroTo Y)).hom a = 1 :=
  integerMap_through_zero_apply (j := j) q _ _ a

/-- An actual level-weak contraction to native zero makes each original integer class the unit. -/
theorem integerContractible_eq_one (q : ℤ) (W : (Carrier.{u, v} (I := I)))
    (hW : weakEquivalences (Carrier (I := I)) (Diagrams.toZero W))
    (a : (integerPiFunctor j q).obj W) : a = 1 := by
  let e := integerPiLevelWeakIso (j := j) q (Diagrams.toZero W) hW
  apply e.groupIsoToMulEquiv.injective
  exact (integerZero_eq_one (j := j) q (e.hom.hom a)).trans (map_one e.hom.hom).symm

/-- Every factorization through an actually contractible native object has a trivial class map. -/
theorem integerMap_through_contractible_apply (q : ℤ) {X Y W : (Carrier.{u, v} (I := I))}
    (f : X ⟶ W) (g : W ⟶ Y) (hW : weakEquivalences (Carrier (I := I)) (Diagrams.toZero W))
    (a : (integerPiFunctor j q).obj X) :
    ((integerPiFunctor j q).map (f ≫ g)).hom a = 1 := by
  rw [Functor.map_comp]
  change ((integerPiFunctor j q).map g).hom
    (((integerPiFunctor j q).map f).hom a) = 1
  rw [integerContractible_eq_one (j := j) q W hW (((integerPiFunctor j q).map f).hom a)]
  exact map_one _

/-- The unchanged original I cone has its actual native level-weak collapse for every source. -/
theorem originalConeCollapse_weak (X : (Carrier.{u, v} (I := I))) :
    weakEquivalences (Carrier (I := I))
      (Diagrams.toZero ((OriginalICone.cone (B := B) (I := Index)).obj X)) := by
  have h := (OriginalICone.contraction_trivialFibration (B := B) X).2
  rw [OriginalICone.contraction_eq_toZero] at h
  exact h

/-- Both original cone factors induce the actual trivial integer map on every original class. -/
theorem integerMap_through_original_cone_apply (q : ℤ) {X Y W : (Carrier.{u, v} (I := I))}
    (f : X ⟶ (OriginalICone.cone (B := B) (I := Index)).obj W)
    (g : (OriginalICone.cone (B := B) (I := Index)).obj W ⟶ Y)
    (a : (integerPiFunctor j q).obj X) :
    ((integerPiFunctor j q).map (f ≫ g)).hom a = 1 :=
  integerMap_through_contractible_apply (j := j) q f g (originalConeCollapse_weak W) a

/-- The complete original cone leg is typed at the actual original cofiber object. -/
def cofiberConeLeg (F : Arrow (Carrier.{u, v} (I := I))) : (cone (I := I)).obj ((Q (I := I)).obj
  F.left) ⟶ (cofiber (I := I)).obj F :=
  (c ((Q (I := I)).mapArrow.obj F)).inl

/-- The original cofiber map retains its complete original Q cone leg. -/
theorem cofiberMap_cone {F G : Arrow (Carrier.{u, v} (I := I))} (m : F ⟶ G) :
    cofiberConeLeg F ≫ (cofiber (I := I)).map m = (cone (I := I)).map ((Q (I := I)).map m.left) ≫
      cofiberConeLeg G :=
  OrdinaryHoChosenPuppe.cofiberMap_cone (cone (I := I)) (ι (I := I)) c hc ((Q (I :=
    I)).mapArrow.map m)

/-- The native zero leg retains the exact original I-Q suspension target. -/
def suspensionZeroLeg (X : (Carrier.{u, v} (I := I))) :
    Diagrams.zeroDiagram ⟶ (originalISuspensionQFunctor (I := I)).obj X :=
  (suspensionCocone ((Q (I := I)).obj X)).inr

/-- The original I-Q cone leg keeps its complete actual suspension target. -/
def suspensionConeLeg (X : (Carrier.{u, v} (I := I))) :
    (cone (I := I)).obj ((Q (I := I)).obj X) ⟶ (originalISuspensionQFunctor (I := I)).obj X :=
  (suspensionCocone ((Q (I := I)).obj X)).inl

/-- The complete original cofiber cone leg maps to the same original suspension cone leg. -/
theorem cofiberConeLeg_boundary (F : Arrow (Carrier.{u, v} (I := I))) :
    cofiberConeLeg F ≫ boundary F = suspensionConeLeg F.left := boundary_cone F

/-- The original inclusion/boundary square retains the native zero leg at its actual target. -/
theorem originalInclusionBoundary (F : Arrow (Carrier.{u, v} (I := I))) :
    inclusion F ≫ boundary F = Diagrams.toZero ((Q (I := I)).obj F.right) ≫ suspensionZeroLeg
      F.left :=
  inclusion_boundary F

/-- The actual chosen boundary retains the full original Q and I-suspension source map. -/
def originalBoundaryNatTrans : (cofiber.{u, v} (I := I)) ⟶
    Arrow.leftFunc ⋙ (originalISuspensionQFunctor (I := I)) where
  app F := boundary F
  naturality _ _ m := boundary_naturality m

/-- The boundary and the proved desuspension compose as whole original natural families. -/
def connectingPlusOneNatTrans (q : ℤ) : (cofiber.{u, v} (I := I)) ⋙ integerPiFunctor j (q + 1) ⟶
    Arrow.leftFunc ⋙ integerPiFunctor j q :=
  Functor.whiskerRight originalBoundaryNatTrans (integerPiFunctor j (q + 1)) ≫
    (Functor.associator Arrow.leftFunc (originalISuspensionQFunctor (I := I))
      (integerPiFunctor j (q + 1))).hom ≫
        Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso (j := j) q).inv

/-- The actual boundary in degree q+1 is desuspended by the entire original I-Q inverse. -/
def connectingPlusOne (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F) ⟶
      (integerPiFunctor j q).obj F.left :=
  (connectingPlusOneNatTrans (j := j) q).app F

/-- The whole family keeps the original chosen boundary and the complete I-Q inverse. -/
theorem connectingPlusOneNatTrans_formula (q : ℤ) :
    connectingPlusOneNatTrans.{u, v} (j := j) q =
      Functor.whiskerRight originalBoundaryNatTrans (integerPiFunctor j (q + 1)) ≫
        (Functor.associator Arrow.leftFunc (originalISuspensionQFunctor (I := I))
          (integerPiFunctor j (q + 1))).hom ≫
            Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso (j := j) q).inv := rfl

/-- Every actual class keeps the original chosen boundary and all I-Q inverse factors. -/
theorem connectingPlusOne_apply (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F)) :
    (connectingPlusOne (j := j) q F).hom a =
      ((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom
        (((integerPiFunctor j (q + 1)).map (boundary F)).hom a) := by
  dsimp only [connectingPlusOne, connectingPlusOneNatTrans, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, originalBoundaryNatTrans,
    Functor.associator]
  rfl

/-- Both components of the original Arrow square retain the same complete connecting square. -/
theorem connectingPlusOne_naturality (q : ℤ) {F G : Arrow (Carrier.{u, v} (I := I))} (m : F ⟶ G) :
    (integerPiFunctor j (q + 1)).map ((cofiber (I := I)).map m) ≫ connectingPlusOne (j := j) q G =
      connectingPlusOne (j := j) q F ≫ (integerPiFunctor j q).map m.left :=
  (connectingPlusOneNatTrans (j := j) q).naturality m

/-- The predecessor degree is transported by its actual integer equality. -/
def integerDegreeNatIso (q r : ℤ) (h : q = r) : integerPiFunctor j q ≅
    integerPiFunctor j r := eqToIso (congrArg (integerPiFunctor j) h)

/-- The predecessor degree retains the complete original integer equality transport. -/
def predecessorDegreeNatIso (q : ℤ) : integerPiFunctor j q ≅
    integerPiFunctor j ((q - 1) + 1) :=
  integerDegreeNatIso (j := j) q ((q - 1) + 1) (by omega)

/-- The actual integer connecting map has source degree q and original target degree q-1. -/
def connecting (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (integerPiFunctor j q).obj ((cofiber (I := I)).obj F) ⟶
      (integerPiFunctor j (q - 1)).obj F.left :=
  (predecessorDegreeNatIso (j := j) q).hom.app ((cofiber (I := I)).obj F) ≫ connectingPlusOne (j
    := j) (q - 1) F

/-- Every canonical connecting component retains the complete predecessor and boundary family. -/
theorem connecting_formula (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    connecting (j := j) q F = (predecessorDegreeNatIso (j := j) q).hom.app ((cofiber (I := I)).obj
      F) ≫
      connectingPlusOne (j := j) (q - 1) F := rfl

/-- The canonical all-integer connecting family retains both original Arrow components. -/
def connectingNatTrans (q : ℤ) : (cofiber.{u, v} (I := I)) ⋙ integerPiFunctor j q ⟶
    Arrow.leftFunc ⋙ integerPiFunctor j (q - 1) :=
  Functor.whiskerLeft (cofiber (I := I)) (predecessorDegreeNatIso (j := j) q).hom ≫
    connectingPlusOneNatTrans (j := j) (q - 1)

/-- The canonical natural family acts by the same entire chosen-boundary connecting map. -/
theorem connectingNatTrans_app (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (connectingNatTrans (j := j) q).app F = connecting (j := j) q F := rfl

/-- Every actual all-integer connecting square retains its original whole-arrow map. -/
theorem connecting_naturality (q : ℤ) {F G : Arrow (Carrier.{u, v} (I := I))} (m : F ⟶ G) :
    (integerPiFunctor j q).map ((cofiber (I := I)).map m) ≫ connecting (j := j) q G =
      connecting (j := j) q F ≫ (integerPiFunctor j (q - 1)).map m.left :=
  (connectingNatTrans (j := j) q).naturality m

/-- Desuspending and resuspending the entire connecting family recovers the original boundary. -/
theorem connectingPlusOneNatTrans_resuspension (q : ℤ) :
    connectingPlusOneNatTrans.{u, v} (j := j) q ≫
        Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso (j := j) q).hom =
      Functor.whiskerRight originalBoundaryNatTrans (integerPiFunctor j (q + 1)) ≫
        (Functor.associator Arrow.leftFunc (originalISuspensionQFunctor (I := I))
          (integerPiFunctor j (q + 1))).hom := by
  rw [connectingPlusOneNatTrans_formula (j := j)]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.comp_id]

/-- The original source/inclusion composite factors through the same actual original I cone. -/
theorem originalSourceInclusion_factors_cone (F : Arrow (Carrier.{u, v} (I := I))) :
    (Q (I := I)).map F.hom ≫ inclusion F =
      (ι (I := I)).app ((Q (I := I)).obj F.left) ≫ (c ((Q (I := I)).mapArrow.obj F)).inl :=
  (c ((Q (I := I)).mapArrow.obj F)).condition.symm

/-- The chosen cofiber maps to the original I cone of its unchanged Q target. -/
def cofiberConeComparison (F : Arrow (Carrier.{u, v} (I := I))) :
    (cofiber (I := I)).obj F ⟶ (cone (I := I)).obj ((Q (I := I)).obj F.right) :=
  OrdinaryHoChosenPuppe.coneComparison (cone (I := I)) (ι (I := I)) c hc ((Q (I :=
    I)).mapArrow.obj F)

/-- The actual cofiber-to-cone comparison retains its full original cone leg. -/
theorem cofiberConeComparison_cone (F : Arrow (Carrier.{u, v} (I := I))) :
    cofiberConeLeg F ≫ cofiberConeComparison F = (cone (I := I)).map ((Q (I := I)).map F.hom) :=
  OrdinaryHoChosenPuppe.coneComparison_cone (cone (I := I)) (ι (I := I)) c hc ((Q (I :=
    I)).mapArrow.obj F)

/-- The same cofiber-to-cone comparison retains its full original target leg. -/
theorem cofiberConeComparison_target (F : Arrow (Carrier.{u, v} (I := I))) :
    inclusion F ≫ cofiberConeComparison F = (ι (I := I)).app ((Q (I := I)).obj F.right) :=
  OrdinaryHoChosenPuppe.coneComparison_target (cone (I := I)) (ι (I := I)) c hc ((Q (I :=
    I)).mapArrow.obj F)

/-- Every entire Arrow square retains both original legs of the actual cofiber-to-cone map. -/
theorem cofiberConeComparison_naturality {F G : Arrow (Carrier.{u, v} (I := I))} (m : F ⟶ G) :
    (cofiber (I := I)).map m ≫ cofiberConeComparison G =
      cofiberConeComparison F ≫ (cone (I := I)).map ((Q (I := I)).map m.right) := by
  apply PushoutCocone.IsColimit.hom_ext (hc ((Q (I := I)).mapArrow.obj F))
  · change cofiberConeLeg F ≫ ((cofiber (I := I)).map m ≫ cofiberConeComparison G) =
      cofiberConeLeg F ≫ (cofiberConeComparison F ≫ (cone (I := I)).map ((Q (I := I)).map m.right))
    rw [← Category.assoc, cofiberMap_cone]
    rw [Category.assoc, cofiberConeComparison_cone, ← Category.assoc,
      cofiberConeComparison_cone, ← (cone (I := I)).map_comp, ← (cone (I := I)).map_comp]
    exact (cone (I := I)).congr_map ((Q (I := I)).mapArrow.map m).w
  · change inclusion F ≫ ((cofiber (I := I)).map m ≫ cofiberConeComparison G) =
      inclusion F ≫ (cofiberConeComparison F ≫ (cone (I := I)).map ((Q (I := I)).map m.right))
    rw [← Category.assoc, ← inclusion_naturality, Category.assoc,
      cofiberConeComparison_target, ← Category.assoc, cofiberConeComparison_target]
    exact (ι (I := I)).naturality ((Q (I := I)).map m.right)

/-- The original boundary/source-suspension composite factors through the actual target I cone. -/
theorem originalBoundarySuspension_factors_cone (F : Arrow (Carrier.{u, v} (I := I))) :
    boundary F ≫ (originalISuspensionQFunctor (I := I)).map F.hom =
      cofiberConeComparison F ≫ (suspensionCocone ((Q (I := I)).obj F.right)).inl :=
  OrdinaryHoChosenPuppe.boundary_suspension_factors_cone
    (cone (I := I)) (ι (I := I)) c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I :=
      I)).mapArrow.obj F)

/-- Both integer functions of Root's original Q Ho Iso agree with the original Q counit Iso. -/
theorem qCounitHoIso_integerIso (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (integerPiHoFunctor j q).mapIso (qCounitHoIso X) =
      (qCounitIntegerNatIso (j := j) q).app X := by
  apply Iso.ext
  change (integerPiHoFunctor j q).map ((H (I := I)).map ((ε (I := I)).app X)) =
    (qCounitIntegerNatIso (j := j) q).hom.app X
  rw [integerPiHoFunctor_map (j := j), qCounitIntegerNatIso_hom_app (j := j)]

/-- The original Q inverse used in the cofiber inclusion is the same integer quotient inverse. -/
theorem qCounitHoIso_integer_inverse (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (integerPiHoFunctor j q).map (qCounitHoIso X).inv =
      (qCounitIntegerNatIso (j := j) q).inv.app X :=
  congrArg (fun e => e.inv) (qCounitHoIso_integerIso (j := j) q X)

/-- The whole source-map family keeps the original Arrow itself on every integer group. -/
def sourceIntegerNatTrans (q : ℤ) : Arrow.leftFunc ⋙ integerPiFunctor j q ⟶
    Arrow.rightFunc ⋙ integerPiFunctor j q :=
  Functor.whiskerRight Arrow.leftToRight (integerPiFunctor j q)

/-- The whole target-inclusion family keeps its original Q inverse and chosen cofiber leg. -/
def inclusionIntegerNatTrans (q : ℤ) :
    Arrow.rightFunc ⋙ integerPiFunctor j q ⟶ (cofiber (I := I)) ⋙ integerPiFunctor j q where
  app F := inclusionInteger (j := j) q F
  naturality _ _ m := inclusionInteger_naturality (j := j) q m

/-- Every inclusion family component is the same complete original Q/inclusion function. -/
theorem inclusionIntegerNatTrans_app (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (inclusionIntegerNatTrans (j := j) q).app F = inclusionInteger (j := j) q F := rfl

/-- Every original source class has trivial image through the Q source and actual inclusion. -/
theorem qSource_inclusion_null (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j q).obj ((Q (I := I)).obj F.left)) :
    ((integerPiFunctor j q).map (inclusion F)).hom
      (((integerPiFunctor j q).map ((Q (I := I)).map F.hom)).hom a) = 1 := by
  change ((integerPiFunctor j q).map ((Q (I := I)).map F.hom) ≫
    (integerPiFunctor j q).map (inclusion F)).hom a = 1
  rw [← Functor.map_comp, originalSourceInclusion_factors_cone]
  exact integerMap_through_original_cone_apply (j := j) q _ _ a

/-- The full original source/inclusion composite is null on every original integer class. -/
theorem source_inclusion_null (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j q).obj F.left) :
    (inclusionInteger (j := j) q F).hom (((integerPiFunctor j q).map F.hom).hom a) = 1 := by
  rw [inclusionInteger_formula (j := j), qCounitHoIso_integer_inverse (j := j)]
  change ((integerPiFunctor j q).map (inclusion F)).hom
    (((qCounitIntegerNatIso (j := j) q).inv.app F.right).hom
      (((integerPiFunctor j q).map F.hom).hom a)) = 1
  have h := ConcreteCategory.congr_hom ((qCounitIntegerNatIso (j := j) q).inv.naturality F.hom) a
  change ((qCounitIntegerNatIso (j := j) q).inv.app F.right).hom
      (((integerPiFunctor j q).map F.hom).hom a) =
    ((integerPiFunctor j q).map ((Q (I := I)).map F.hom)).hom
      (((qCounitIntegerNatIso (j := j) q).inv.app F.left).hom a) at h
  rw [h]
  exact qSource_inclusion_null (j := j) q F _

/-- The full inclusion/boundary composite is null through the same original native zero. -/
theorem inclusion_connectingPlusOne_null (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j (q + 1)).obj F.right) :
    (connectingPlusOne (j := j) q F).hom (((inclusionIntegerNatTrans (j := j) (q + 1)).app F).hom
      a) = 1 := by
  rw [connectingPlusOne_apply (j := j), inclusionIntegerNatTrans_app (j := j),
    inclusionInteger_formula (j := j), qCounitHoIso_integer_inverse (j := j)]
  let b : (integerPiFunctor j (q + 1)).obj ((Q (I := I)).obj F.right) :=
    ((qCounitIntegerNatIso (j := j) (q + 1)).inv.app F.right).hom a
  have h : ((integerPiFunctor j (q + 1)).map (boundary F)).hom
      (((integerPiFunctor j (q + 1)).map (inclusion F)).hom b) = 1 := by
    change ((integerPiFunctor j (q + 1)).map (inclusion F) ≫
      (integerPiFunctor j (q + 1)).map (boundary F)).hom b = 1
    rw [← Functor.map_comp, originalInclusionBoundary]
    exact integerMap_through_zero_apply (j := j) (q + 1)
      (Diagrams.toZero ((Q (I := I)).obj F.right)) (suspensionZeroLeg F.left) b
  change ((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom
    (((integerPiFunctor j (q + 1)).map (boundary F)).hom
      (((integerPiFunctor j (q + 1)).map (inclusion F)).hom b)) = 1
  rw [h]
  exact map_one _

/-- The actual boundary/source-suspension map is null on every original integer class. -/
theorem originalBoundarySuspension_null (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j q).obj ((cofiber (I := I)).obj F)) :
    ((integerPiFunctor j q).map ((originalISuspensionQFunctor (I := I)).map F.hom)).hom
      (((integerPiFunctor j q).map (boundary F)).hom a) = 1 := by
  change ((integerPiFunctor j q).map (boundary F) ≫
    (integerPiFunctor j q).map ((originalISuspensionQFunctor (I := I)).map F.hom)).hom a = 1
  rw [← Functor.map_comp, originalBoundarySuspension_factors_cone]
  exact integerMap_through_original_cone_apply (j := j) q _ _ a

/-- The original connecting/source composite is null with no extra condition on the spectrum. -/
theorem connectingPlusOne_source_null (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F)) :
    ((integerPiFunctor j q).map F.hom).hom ((connectingPlusOne (j := j) q F).hom a) = 1 := by
  rw [connectingPlusOne_apply (j := j)]
  have h := ConcreteCategory.congr_hom
    (integerISuspensionPiNatIso_inv_naturality (j := j) q F.hom)
    (((integerPiFunctor j (q + 1)).map (boundary F)).hom a)
  change ((integerISuspensionPiNatIso (j := j) q).inv.app F.right).hom
      (((integerPiFunctor j (q + 1)).map
        ((originalISuspensionQFunctor (I := I)).map F.hom)).hom
          (((integerPiFunctor j (q + 1)).map (boundary F)).hom a)) =
    ((integerPiFunctor j q).map F.hom).hom
      (((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom
        (((integerPiFunctor j (q + 1)).map (boundary F)).hom a)) at h
  rw [← h, originalBoundarySuspension_null (j := j)]
  exact map_one _

/-- All actual inclusion functions preserve every literal integer-equality transport. -/
theorem integerDegree_inclusion_naturality (q r : ℤ) (h : q = r) :
    inclusionIntegerNatTrans.{u, v} (j := j) q ≫
        Functor.whiskerLeft (cofiber (I := I)) (integerDegreeNatIso (j := j) q r h).hom =
      Functor.whiskerLeft Arrow.rightFunc (integerDegreeNatIso (j := j) q r h).hom ≫
        inclusionIntegerNatTrans (j := j) r := by
  cases h
  change inclusionIntegerNatTrans (j := j) q ≫
      Functor.whiskerLeft (cofiber (I := I)) (𝟙 (integerPiFunctor j q)) =
    Functor.whiskerLeft Arrow.rightFunc (𝟙 (integerPiFunctor j q)) ≫
      inclusionIntegerNatTrans (j := j) q
  rw [Functor.whiskerLeft_id', Functor.whiskerLeft_id',
    Category.comp_id, Category.id_comp]

/-- The canonical inclusion/connecting composite is null in every original integer degree. -/
theorem inclusion_connecting_null (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j q).obj F.right) :
    (connecting (j := j) q F).hom (((inclusionIntegerNatTrans (j := j) q).app F).hom a) = 1 := by
  have h := ConcreteCategory.congr_hom (congr_app
    (integerDegree_inclusion_naturality (j := j) q ((q - 1) + 1) (by omega)) F) a
  change ((predecessorDegreeNatIso (j := j) q).hom.app ((cofiber (I := I)).obj F)).hom
      (((inclusionIntegerNatTrans (j := j) q).app F).hom a) =
    ((inclusionIntegerNatTrans (j := j) ((q - 1) + 1)).app F).hom
      (((predecessorDegreeNatIso (j := j) q).hom.app F.right).hom a) at h
  change (connectingPlusOne (j := j) (q - 1) F).hom
    (((predecessorDegreeNatIso (j := j) q).hom.app ((cofiber (I := I)).obj F)).hom
      (((inclusionIntegerNatTrans (j := j) q).app F).hom a)) = 1
  rw [h]
  exact inclusion_connectingPlusOne_null (j := j) (q - 1) F _

/-- The canonical connecting/source composite is null with its full predecessor degree map. -/
theorem connecting_source_null (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j q).obj ((cofiber (I := I)).obj F)) :
    ((integerPiFunctor j (q - 1)).map F.hom).hom ((connecting (j := j) q F).hom a) = 1 := by
  change ((integerPiFunctor j (q - 1)).map F.hom).hom
    ((connectingPlusOne (j := j) (q - 1) F).hom
      (((predecessorDegreeNatIso (j := j) q).hom.app ((cofiber (I := I)).obj F)).hom a)) = 1
  exact connectingPlusOne_source_null (j := j) (q - 1) F _

/-- The actual group null function is the constant group unit, with no commutativity condition. -/
def trivialGroupMap (G K : GrpCat.{v}) : G ⟶ K :=
  GrpCat.ofHom
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => (one_mul (1 : K)).symm }

/-- The entire original source/inclusion morphism is the actual trivial group morphism. -/
theorem source_inclusion_null_map (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (sourceIntegerNatTrans (j := j) q ≫ inclusionIntegerNatTrans (j := j) q).app F =
      trivialGroupMap ((Arrow.leftFunc ⋙ integerPiFunctor j q).obj F)
        (((cofiber (I := I)) ⋙ integerPiFunctor j q).obj F) := by
  apply GrpCat.hom_ext
  ext a
  exact source_inclusion_null (j := j) q F a

/-- The entire canonical inclusion/connecting morphism is the same actual group null function. -/
theorem inclusion_connecting_null_map (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (inclusionIntegerNatTrans (j := j) q ≫ connectingNatTrans (j := j) q).app F =
      trivialGroupMap ((Arrow.rightFunc ⋙ integerPiFunctor j q).obj F)
        ((Arrow.leftFunc ⋙ integerPiFunctor j (q - 1)).obj F) := by
  apply GrpCat.hom_ext
  ext a
  exact inclusion_connecting_null (j := j) q F a

/-- The entire canonical connecting/source morphism retains its actual group null function. -/
theorem connecting_source_null_map (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (connectingNatTrans (j := j) q ≫ sourceIntegerNatTrans (j := j) (q - 1)).app F =
      trivialGroupMap (((cofiber (I := I)) ⋙ integerPiFunctor j q).obj F)
        ((Arrow.rightFunc ⋙ integerPiFunctor j (q - 1)).obj F) := by
  apply GrpCat.hom_ext
  ext a
  exact connecting_source_null (j := j) q F a


end HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerMaps
