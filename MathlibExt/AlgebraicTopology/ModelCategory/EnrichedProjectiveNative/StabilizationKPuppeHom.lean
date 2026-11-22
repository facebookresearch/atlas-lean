/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalCofiberNullity
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeHomSequence

/-!
# Original native Puppe Hom tests and positive suspension shifts

Apply the constructed unbounded Puppe sequence to the same original
whole-arrow cofibrant replacement and I-cone cocones. Weakness of the
literal suspension of weak maps is proved on those actual cocones.
It transports the original suspension-after-Q Omega tests to cofibrant
arrows and hence to every positive suspension iterate after the same Q.

These are prerequisites for original chosen-fiber nullity. This file
does not assert the integer-indexed fiber sequence, its negative
delooping comparisons, or weakness of the original chosen fiber collapse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.FiberHomTests

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

local notation "cone" => OriginalICone.cone (B := B) (I := I)
local notation "ι" => OriginalICone.inclusion (B := B) (I := I)
local notation "c" => OriginalISuspension.cocone (B := B) (I := I)
local notation "hc" => OriginalISuspension.coconeIsColimit (B := B) (I := I)

attribute [local instance] Native.modelCategory

omit B in
private instance nativeZero : HasZeroObject (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  Diagrams.nativeHasZeroObject

private theorem coneCollapse_weak (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

/-- The entire original Q Arrow is retained at every stage of the Puppe functor. -/
def originalQPuppeStage (n : ℕ) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
      Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  (Replacement.cofibrantReplacement (B := B) (A := I)).mapArrow ⋙
    OrdinaryHoChosenPuppeHomSequence.stageFunctor cone ι c hc n

/-- Every native carrier and original Arrow action is retained at the given unbounded stage. -/
def originalQPuppeTerm (n : ℕ) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} I :=
  originalQPuppeStage (B := B) n ⋙ Arrow.leftFunc

/-- Exactness at every actual native Q Puppe stage and every level-homotopy target. -/
theorem originalQPuppe_exact_at (n : ℕ)
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (g : OrdinaryHoChosenPuppeHomSequence.homTerm cone ι c hc (n + 1)
      ((Replacement.cofibrantReplacement (B := B)).mapArrow.obj F) E) :
    (∃ h : OrdinaryHoChosenPuppeHomSequence.homTerm cone ι c hc (n + 2)
        ((Replacement.cofibrantReplacement (B := B)).mapArrow.obj F) E,
      OrdinaryHoChosenPuppeHomSequence.restriction cone ι c hc (n + 1)
        ((Replacement.cofibrantReplacement (B := B)).mapArrow.obj F) E h = g) ↔
      OrdinaryHoChosenPuppeHomSequence.restriction cone ι c hc n
          ((Replacement.cofibrantReplacement (B := B)).mapArrow.obj F) E g =
        OrdinaryHoCofiberKernel.nullHom ((originalQPuppeTerm (B := B) n).obj F) E := by
  let _ : IsCofibrant ((Replacement.cofibrantReplacement (B := B)).mapArrow.obj F).left := by
    change IsCofibrant ((Replacement.cofibrantReplacement (B := B)).obj F.left)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) F.left
  let _ : IsCofibrant ((Replacement.cofibrantReplacement (B := B)).mapArrow.obj F).right := by
    change IsCofibrant ((Replacement.cofibrantReplacement (B := B)).obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) F.right
  let _ : IsFibrant E := Native.allObjectsFibrant E
  exact OrdinaryHoChosenPuppeHomSequence.exact_at
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone ι c hc
    (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => coneCollapse_weak X) n
    ((Replacement.cofibrantReplacement (B := B)).mapArrow.obj F) E g

/-- Literal original I suspension of a weak cofibrant arrow is level weak. -/
theorem originalISuspensionMap_weak {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f] :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((OriginalISuspension.suspension (B := B)).map f) := by
  let _ : Cofibration ((ι).app X) := (cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)
  let _ : Cofibration ((ι).app Y) := (cofibration_iff _).mpr (OriginalICone.inclusion_cofibration Y)
  exact OrdinaryHoChosenPuppeRotation.suspensionMap_weak_of_cofibrant cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero f (coneCollapse_weak X) (coneCollapse_weak Y)

/-- The literal original I suspension preserves Omega tests on cofibrant arrows.
Both comparison endpoint functions are the suspensions of the original Q counits. -/
theorem originalISuspensionMap_omegaTests_of_cofibrant
    (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] (hf : omegaTests s f) :
    omegaTests s ((OriginalISuspension.suspension (B := B)).map f) := by
  let Q := Replacement.cofibrantReplacement (B := B) (A := I)
  let S := OriginalISuspension.suspension (B := B) (I := I)
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement (B := B) X
  let _ : IsCofibrant (Q.obj Y) := Replacement.isCofibrant_cofibrantReplacement (B := B) Y
  let _ : IsCofibrant ((𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X) :=
    inferInstanceAs (IsCofibrant X)
  let _ : IsCofibrant ((𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y) :=
    inferInstanceAs (IsCofibrant Y)
  let _ : WeakEquivalence (ε.app X) := (weakEquivalence_iff _).mpr
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)
  let _ : WeakEquivalence (ε.app Y) := (weakEquivalence_iff _).mpr
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences Y)
  let _ : IsIso (H.map (S.map (ε.app X))) :=
    Localization.inverts H _ (S.map (ε.app X)) (originalISuspensionMap_weak (ε.app X))
  let _ : IsIso (H.map (S.map (ε.app Y))) :=
    Localization.inverts H _ (S.map (ε.app Y)) (originalISuspensionMap_weak (ε.app Y))
  have hQ := originalISuspensionQMap_omegaTests (B := B) s f hf
  intro E hE
  let W : MorphismProperty (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
    ((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
      (yoneda.obj (H.obj E))).unop
  have hQS : W (H.map (S.map (Q.map f))) := by
    change IsIso ((yoneda.obj (H.obj E)).map (H.map (S.map (Q.map f))).op)
    exact (isIso_iff_bijective _).mpr (hQ E hE)
  let a : Arrow.mk (H.map (S.map (Q.map f))) ≅ Arrow.mk (H.map (S.map f)) :=
    Arrow.isoMk (asIso (H.map (S.map (ε.app X))))
      (asIso (H.map (S.map (ε.app Y)))) (by
        change H.map (S.map (ε.app X)) ≫ H.map (S.map f) =
          H.map (S.map (Q.map f)) ≫ H.map (S.map (ε.app Y))
        simpa only [Functor.map_comp] using
          (H.congr_map (S.congr_map
            (Replacement.cofibrantReplacementCounit_naturality f))).symm)
  have hS := (W.arrow_mk_iso_iff a).mp hQS
  exact (isIso_iff_bijective _).mp hS

/-- The same original I suspension has cofibrant output, by its actual zero-source pushout leg. -/
theorem originalISuspension_obj_cofibrant (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsCofibrant ((OriginalISuspension.suspension (B := B)).obj X) := by
  let _ : IsCofibrant (Diagrams.zeroDiagram (A := I)) := by
    rw [isCofibrant_iff_of_isInitial (𝟙 Diagrams.zeroDiagram) Diagrams.zeroDiagramIsInitial]
    infer_instance
  let _ : Cofibration ((ι).app X) := (cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)
  let F := Arrow.mk (OrdinaryHoChosenPuppe.toZero
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero X)
  let _ : Cofibration ((ι).app F.left) := inferInstanceAs (Cofibration ((ι).app X))
  let _ : IsCofibrant F.right :=
    inferInstanceAs (IsCofibrant (Diagrams.zeroDiagram (A := I)))
  let _ : Cofibration (c F).inr := OrdinaryHoChosenPuppe.cofiberTarget_cofibration cone ι c hc F
  exact isCofibrant_of_cofibration (c F).inr

/-- Positive suspension iterates use the original Q once
and the actual I suspension at every step. -/
def originalQSuspensionIterate : ℕ →
    (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I
  | 0 => Replacement.cofibrantReplacement (B := B)
  | n + 1 => originalQSuspensionIterate n ⋙ OriginalISuspension.suspension (B := B)

/-- All original positive iterate carriers are cofibrant. -/
theorem originalQSuspensionIterate_obj_cofibrant (n : ℕ)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsCofibrant ((originalQSuspensionIterate (B := B) n).obj X) := by
  cases n with
  | zero => exact Replacement.isCofibrant_cofibrantReplacement (B := B) X
  | succ n =>
    exact originalISuspension_obj_cofibrant ((originalQSuspensionIterate (B := B) n).obj X)

/-- Every nonnegative original suspension iterate preserves all original Omega-target tests. -/
theorem originalQSuspensionIterate_omegaTests (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) (hf : omegaTests s f) (n : ℕ) :
    omegaTests s ((originalQSuspensionIterate (B := B) n).map f) := by
  induction n with
  | zero => exact (cofibrantReplacement_map_localTest_iff (B := B) s f).mpr hf
  | succ n hn =>
    let _ := originalQSuspensionIterate_obj_cofibrant (B := B) n X
    let _ := originalQSuspensionIterate_obj_cofibrant (B := B) n Y
    exact originalISuspensionMap_omegaTests_of_cofibrant s
      ((originalQSuspensionIterate (B := B) n).map f) hn

/-- The original chosen cofiber of every positive suspension iterate of the same Q arrow. -/
def originalQSuspensionCofiber (n : ℕ) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} I :=
  (originalQSuspensionIterate (B := B) n).mapArrow ⋙
    OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc

/-- The actual collapse of each such chosen cofiber to the unchanged native zero diagram. -/
def originalQSuspensionCofiberCollapse (n : ℕ) :
    originalQSuspensionCofiber (B := B) n ⟶
      (Functor.const (Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))).obj
        Diagrams.zeroDiagram where
  app F := Diagrams.toZero ((originalQSuspensionCofiber (B := B) n).obj F)
  naturality _ _ _ := Diagrams.zeroDiagramIsTerminal.hom_ext _ _

/-- Every map from each actual positive-iterate Q cofiber into every Omega target is null. -/
theorem originalQSuspensionCofiberHom_eq_null (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) (hf : omegaTests s f)
    (n : ℕ) (E : EnrichedFunctorCat PointedCGWH.{u, v} I) (hE : IsOmega s E)
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((originalQSuspensionCofiber (B := B) n).obj (Arrow.mk f)) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E) :
    g = OrdinaryHoCofiberKernel.nullHom
      ((originalQSuspensionCofiber (B := B) n).obj (Arrow.mk f)) E := by
  let F := (originalQSuspensionIterate (B := B) n).mapArrow.obj (Arrow.mk f)
  let _ : IsCofibrant F.left := originalQSuspensionIterate_obj_cofibrant (B := B) n X
  let _ : IsCofibrant F.right := originalQSuspensionIterate_obj_cofibrant (B := B) n Y
  let _ : Cofibration ((ι).app F.left) := (cofibration_iff _).mpr
    (OriginalICone.inclusion_cofibration F.left)
  let _ : IsFibrant E := Native.allObjectsFibrant E
  have hF := originalQSuspensionIterate_omegaTests (B := B) s f hf n
  have hS := originalISuspensionMap_omegaTests_of_cofibrant (B := B) s F.hom hF
  exact OrdinaryHoPuppeCofiberNull.cofiberHom_eq_null
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone ι c hc F E
    (coneCollapse_weak F.left) (coneCollapse_weak F.right) (hF E hE).1 (hS E hE).2 g

/-- All positive-iterate original Q cofiber collapses preserve the full Omega-target tests. -/
theorem originalQSuspensionCofiberCollapse_omegaTests (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) (hf : omegaTests s f) (n : ℕ) :
    omegaTests s ((originalQSuspensionCofiberCollapse (B := B) n).app (Arrow.mk f)) := by
  intro E hE
  let _ : IsFibrant E := Native.allObjectsFibrant E
  let W := (originalQSuspensionCofiber (B := B) n).obj (Arrow.mk f)
  have hUnique : Subsingleton
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj W ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E) :=
    ⟨fun g h => (originalQSuspensionCofiberHom_eq_null (B := B) s f hf n E hE g).trans
      (originalQSuspensionCofiberHom_eq_null (B := B) s f hf n E hE h).symm⟩
  have hCollapse : (originalQSuspensionCofiberCollapse (B := B) n).app (Arrow.mk f) =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero W :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse]
  exact (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero W E).mpr hUnique

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.FiberHomTests
