/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalSuspensionPreservation
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoPuppeCofiberNull

/-!
# Original Q cofibers are null at every Omega target

Use the original I-cone and its chosen Puppe pushouts on the entire original
cofibrant replacement arrow. The original test equivalence and its proved
suspension tests supply the two actual Puppe restrictions. Every map from
that same cofiber to an original Omega target is the null homotopy class;
the actual cofiber-to-zero collapse therefore preserves the Omega tests.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.CofiberNullity

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I
attribute [local instance] Native.modelCategory

omit B in
private instance nativeZero : HasZeroObject (D (I := I)) := Diagrams.nativeHasZeroObject

/-- The original chosen Puppe cofiber of the entire original Q arrow. -/
def cofiberQ : Arrow (D (I := I)) ⥤ D (I := I) :=
  (Replacement.cofibrantReplacement (B := B) (A := I)).mapArrow ⋙
    OrdinaryHoChosenPuppe.cofiberFunctor
      (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
      (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))

/-- The natural collapse of the original Q cofiber to the unchanged native zero. -/
def collapse : cofiberQ (B := B) (I := I) ⟶
    (Functor.const (Arrow (D (I := I)))).obj Diagrams.zeroDiagram where
  app F := Diagrams.toZero ((cofiberQ (B := B)).obj F)
  naturality _ _ _ := Diagrams.zeroDiagramIsTerminal.hom_ext _ _

/-- The original I-cone contraction is the actual weak collapse used by Puppe exactness. -/
private theorem coneCollapse_weak (X : D (I := I)) :
    weakEquivalences (D (I := I))
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((OriginalICone.cone (B := B)).obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((OriginalICone.cone (B := B)).obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

/-- Every original level-homotopy map from the same Q cofiber to an Omega target
is the actual null class. -/
theorem cofiberQHom_eq_null {X Y : D (I := I)} (f : X ⟶ Y) (hf : omegaTests s f)
    (E : D (I := I)) (hE : IsOmega s E)
    (g : (toHomotopyCategory (D (I := I))).obj ((cofiberQ (B := B)).obj (Arrow.mk f)) ⟶
      (toHomotopyCategory (D (I := I))).obj E) :
    g = OrdinaryHoCofiberKernel.nullHom ((cofiberQ (B := B)).obj (Arrow.mk f)) E := by
  let Q := Replacement.cofibrantReplacement (B := B) (A := I)
  let F := Arrow.mk (Q.map f)
  let _ : IsCofibrant F.left := Replacement.isCofibrant_cofibrantReplacement (B := B) X
  let _ : IsCofibrant F.right := Replacement.isCofibrant_cofibrantReplacement (B := B) Y
  let _ : Cofibration ((OriginalICone.inclusion (B := B)).app F.left) :=
    (cofibration_iff _).mpr (OriginalICone.inclusion_cofibration F.left)
  let _ : IsFibrant E := Native.allObjectsFibrant E
  have hQ := (cofibrantReplacement_map_localTest_iff (B := B) s f).mpr hf
  have hS := originalISuspensionQMap_omegaTests (B := B) s f hf
  exact OrdinaryHoPuppeCofiberNull.cofiberHom_eq_null
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    F E (coneCollapse_weak F.left) (coneCollapse_weak F.right)
    (hQ E hE).1 (hS E hE).2 g

/-- An original Omega-test weak arrow has Omega-test null original Q cofiber. -/
theorem collapse_omegaTests {X Y : D (I := I)} (f : X ⟶ Y) (hf : omegaTests s f) :
    omegaTests s ((collapse (B := B)).app (Arrow.mk f)) := by
  intro E hE
  let _ : IsFibrant E := Native.allObjectsFibrant E
  let W := (cofiberQ (B := B)).obj (Arrow.mk f)
  have hUnique : Subsingleton ((toHomotopyCategory (D (I := I))).obj W ⟶
      (toHomotopyCategory (D (I := I))).obj E) :=
    ⟨fun g h => (cofiberQHom_eq_null (B := B) s f hf E hE g).trans
      (cofiberQHom_eq_null (B := B) s f hf E hE h).symm⟩
  have hCollapse : (collapse (B := B)).app (Arrow.mk f) =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero W :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse]
  exact (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero W E).mpr hUnique

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.CofiberNullity
