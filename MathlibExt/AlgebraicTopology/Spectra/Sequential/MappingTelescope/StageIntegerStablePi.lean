/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePi

/-!
# Original level weakness and every original MC transition on integer stable pi

The SAME caller-B native level model gives actual weak pointed level
maps. Genuine homotopy-group invariance constructs the whole Iso of
the ONE original diagonal, with its full hom equal to the actual map.
The SAME genuine Group colimit then gives integer stable-pi Isos.
Every original MC projection and exact transition factorization, joined
to the already proved actual R-unit Iso, give full stage transition
Isos with all original spectrum input maps and choices retained.
No stable-model or Omega-test recognition law is supplied or inferred.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

private theorem originalFactorizationIsoHom
    {C : Type uC} [Category.{vC} C] {A B D E : C}
    (e : A ≅ D) (u : D ≅ E) (p : B ≅ E) (a : A ⟶ B)
    (h : a ≫ p.hom = e.hom ≫ u.hom) : (e ≪≫ u ≪≫ p.symm).hom = a := by
  apply (cancel_mono p.hom).mp
  change (e.hom ≫ u.hom ≫ p.inv) ≫ p.hom = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h.symm

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop (iterate iterateUnit iterateUnit_app)
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The SAME original caller-B level weak map is weak at EVERY actual original pointed level. -/
theorem levelWeakPointedLevelWeakEquivalence
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) (m : ℕ) :
    WeakEquivalence (PointedCGWH.SequentialSpectrum.levelMap f m) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at hf
  have h := (EvaluationTransfer.evaluationProperty_iff
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} =>
      CategoryTheory.EnrichedFunctorCat.evaluation a)
    (weakEquivalences PointedCGWH.{u, v}) f).mp hf
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m))

/-- The actual original weak level map gives BOTH genuine positive homotopy group Iso functions. -/
def levelWeakPositiveIso
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) (m k : ℕ) :
    (piNPositiveFunctor k).obj (X.level m) ≅ (piNPositiveFunctor k).obj (Y.level m) :=
  (piNPositiveMulEquivOfWeakEquivalence k (PointedCGWH.SequentialSpectrum.levelMap f m)
    (levelWeakPointedLevelWeakEquivalence f hf m)).toGrpIso

/-- The ENTIRE level-group Iso hom is the SAME actual original positive homotopy map. -/
theorem levelWeakPositiveIso_hom
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) (m k : ℕ) :
    (levelWeakPositiveIso f hf m k).hom =
      (piNPositiveFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap f m) := by
  apply GrpCat.hom_ext
  ext a
  exact piNPositiveMulEquivOfWeakEquivalence_apply k _
    (levelWeakPointedLevelWeakEquivalence f hf m) a

/-- All original varying levels, degrees and finite maps form the SAME genuine diagonal Iso. -/
def levelWeakDiagonalIso (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    diagonalDiagram X m k ≅ diagonalDiagram Y m k :=
  NatIso.ofComponents (fun n => levelWeakPositiveIso f hf (m + n) (k + n))
    (fun φ => by
      rw [levelWeakPositiveIso_hom, levelWeakPositiveIso_hom]
      exact ((diagonalDiagramFunctor m k).map f).naturality φ)

/-- The ENTIRE original diagonal Iso hom is the SAME original actual diagonal map. -/
theorem levelWeakDiagonalIso_hom (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    (levelWeakDiagonalIso m k f hf).hom = (diagonalDiagramFunctor m k).map f := by
  apply NatTrans.ext
  funext n
  exact levelWeakPositiveIso_hom f hf (m + n) (k + n)

/-- BOTH complete original integer pi Iso maps come from the SAME genuine Group colimit functor. -/
def integerStablePiLevelWeakIso (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    (integerStablePiFunctor q).obj X ≅ (integerStablePiFunctor q).obj Y :=
  GrpCat.FilteredColimits.colimitFunctor.mapIso
    (levelWeakDiagonalIso (integerTailLevel q) (integerTailPositiveIndex q) f hf)

/-- The ENTIRE level-weak integer Iso hom is the original actual integer stable-pi map. -/
theorem integerStablePiLevelWeakIso_hom (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    (integerStablePiLevelWeakIso q f hf).hom = (integerStablePiFunctor q).map f :=
  GrpCat.FilteredColimits.colimitFunctor.congr_map
    (levelWeakDiagonalIso_hom (integerTailLevel q) (integerTailPositiveIndex q) f hf)

/-- In EVERY original integer degree the SAME actual level weak map induces a genuine Iso. -/
theorem integerStablePiLevelWeak_isIso (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    IsIso ((integerStablePiFunctor q).map f) :=
  (integerStablePiLevelWeakIso_hom q f hf) ▸ (integerStablePiLevelWeakIso q f hf).isIso_hom

/-- The SAME caller-B native level weak class satisfies all original integer pi-star tests. -/
theorem levelWeak_le_integerPiStarEquivalences :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ≤ integerPiStarEquivalences := by
  intro X Y f hf
  exact (integerPiStarEquivalences_iff f).mpr (fun q => integerStablePiLevelWeak_isIso q f hf)

/-- Every original MC projection gives BOTH genuine integer stable-pi Iso functions. -/
def projectionIntegerStablePiIso (q : ℤ) (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj ((stage n).functor.obj X) ≅
      (integerStablePiFunctor q).obj ((iterate n).obj X) :=
  integerStablePiLevelWeakIso q ((projection n).app X)
    ((HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence n X))

/-- The ENTIRE original MC projection Iso hom is the SAME actual integer projection map. -/
theorem projectionIntegerStablePiIso_hom (q : ℤ) (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (projectionIntegerStablePiIso q n X).hom =
      (integerStablePiFunctor q).map ((projection n).app X) :=
  integerStablePiLevelWeakIso_hom q ((projection n).app X)
    ((HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence n X))

/-- ALL original spectrum maps retain the whole original MC projection integer Iso. -/
def projectionIntegerStablePiNatIso (q : ℤ) (n : ℕ) :
    (stage.{u, v} n).functor ⋙ integerStablePiFunctor q ≅ iterate n ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => projectionIntegerStablePiIso q n X) (fun f => by
    rw [projectionIntegerStablePiIso_hom, projectionIntegerStablePiIso_hom]
    exact (Functor.whiskerRight (projection n) (integerStablePiFunctor q)).naturality f)

/-- The ENTIRE original projection NatIso hom keeps the full original projection map family. -/
theorem projectionIntegerStablePiNatIso_hom (q : ℤ) (n : ℕ) :
    (projectionIntegerStablePiNatIso.{u, v} q n).hom =
      Functor.whiskerRight (projection n) (integerStablePiFunctor q) := by
  apply NatTrans.ext
  funext X
  exact projectionIntegerStablePiIso_hom q n X

omit B in
/-- Every SAME original iterate unit satisfies all original integer stable-pi tests. -/
theorem iterateUnit_integerPiStarEquivalence (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    integerPiStarEquivalences ((iterateUnit n).app X) := by
  rw [iterateUnit_app]
  exact rUnit_integerPiStarEquivalence ((iterate n).obj X)

/-- BOTH full original MC transition Iso functions use the SAME projection/unit/projection word. -/
def transitionIntegerStablePiIso (q : ℤ) (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj ((stage n).functor.obj X) ≅
      (integerStablePiFunctor q).obj ((stage (n + 1)).functor.obj X) :=
  projectionIntegerStablePiIso q n X ≪≫ integerStablePiRUnitIso q ((iterate n).obj X) ≪≫
    (projectionIntegerStablePiIso q (n + 1) X).symm

/-- The ENTIRE original MC transition Iso hom is the SAME actual integer transition map. -/
theorem transitionIntegerStablePiIso_hom (q : ℤ) (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (transitionIntegerStablePiIso q n X).hom =
      (integerStablePiFunctor q).map ((transition n).app X) := by
  let Q := integerStablePiFunctor.{u, v} q
  have h := congr_app (transition_projection n) X
  have hm : Q.map ((transition n).app X) ≫ Q.map ((projection (n + 1)).app X) =
      Q.map ((projection n).app X) ≫ Q.map ((iterateUnit n).app X) :=
    (Q.map_comp _ _).symm.trans ((Q.congr_map h).trans (Q.map_comp _ _))
  have hu : (integerStablePiRUnitIso q ((iterate n).obj X)).hom =
      Q.map ((iterateUnit n).app X) :=
    (integerStablePiRUnitIso_hom q ((iterate n).obj X)).trans
      (Q.congr_map (iterateUnit_app n X).symm)
  have hf : Q.map ((transition n).app X) ≫ (projectionIntegerStablePiIso q (n + 1) X).hom =
      (projectionIntegerStablePiIso q n X).hom ≫
        (integerStablePiRUnitIso q ((iterate n).obj X)).hom :=
    (congrArg (fun f => Q.map ((transition n).app X) ≫ f)
      (projectionIntegerStablePiIso_hom q (n + 1) X)).trans
        (hm.trans (congrArg₂ (fun f g => f ≫ g)
          (projectionIntegerStablePiIso_hom q n X).symm hu.symm))
  exact originalFactorizationIsoHom (projectionIntegerStablePiIso q n X)
    (integerStablePiRUnitIso q ((iterate n).obj X))
    (projectionIntegerStablePiIso q (n + 1) X) (Q.map ((transition n).app X)) hf

/-- All original spectrum maps retain the WHOLE original MC transition integer Iso. -/
def transitionIntegerStablePiNatIso (q : ℤ) (n : ℕ) :
    (stage.{u, v} n).functor ⋙ integerStablePiFunctor q ≅
      (stage (n + 1)).functor ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => transitionIntegerStablePiIso q n X) (fun f => by
    rw [transitionIntegerStablePiIso_hom, transitionIntegerStablePiIso_hom]
    exact (Functor.whiskerRight (transition n) (integerStablePiFunctor q)).naturality f)

/-- The ENTIRE transition NatIso hom equals the SAME actual original transition map family. -/
theorem transitionIntegerStablePiNatIso_hom (q : ℤ) (n : ℕ) :
    (transitionIntegerStablePiNatIso.{u, v} q n).hom =
      Functor.whiskerRight (transition n) (integerStablePiFunctor q) := by
  apply NatTrans.ext
  funext X
  exact transitionIntegerStablePiIso_hom q n X

/-- EVERY actual original MC transition induces an Iso in EVERY original integer degree. -/
theorem transitionIntegerStablePi_isIso (q : ℤ) (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso ((integerStablePiFunctor q).map ((transition n).app X)) :=
  (transitionIntegerStablePiIso_hom q n X) ▸ (transitionIntegerStablePiIso q n X).isIso_hom

/-- Every SAME original MC transition satisfies ALL actual original integer pi-star tests. -/
theorem transition_integerPiStarEquivalence (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    integerPiStarEquivalences ((transition n).app X) :=
  (integerPiStarEquivalences_iff _).mpr (fun q => transitionIntegerStablePi_isIso q n X)

end PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
