/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CoproductCofiber
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberIntegerMaps
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberCofiberComparison

/-!
# The actual whole-arrow Q cofiber of a coproduct inclusion

The original cofibrant replacement counit is a whole Arrow map. Its
actual chosen-cofiber map is weak for cofibrant original summands and
retains the original target inclusion. Composing with the unchanged
cone collapse gives the original right-summand cofiber comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductQCofiberGeometry

open PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductCofiberGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index)
variable (X Y : PointedCGWH.SequentialSpectrum.{u, v})

/-- The same original whole replacement-counit Arrow map on the coproduct inclusion. -/
def counitArrow : Q.mapArrow.obj (arrow X Y) ⟶ arrow X Y :=
  Arrow.homMk (ε.app X) (ε.app (X ⨿ Y)) (ε.naturality (coprod.inl : X ⟶ X ⨿ Y)).symm

/-- The actual whole chosen-cofiber map induced by the original replacement counit. -/
def toConeCofiber : (cofiber (B := B)).obj (arrow X Y) ⟶ coneCofiber (B := B) X Y :=
  OrdinaryHoChosenPuppe.cofiberMap (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B)) (counitArrow X Y)

/-- The full original target inclusion keeps the same whole replacement-counit target map. -/
theorem toConeCofiber_target :
    inclusion (B := B) (arrow X Y) ≫ toConeCofiber X Y =
      ε.app (X ⨿ Y) ≫ (OriginalISuspension.cocone (B := B) (arrow X Y)).inr :=
  OrdinaryHoChosenPuppe.cofiberMap_target _ _ _ _ (counitArrow X Y)

/-- The original Q cofiber maps to the original right summand by the same cone collapse. -/
def collapse : (cofiber (B := B)).obj (arrow X Y) ⟶ Y :=
  toConeCofiber X Y ≫ CoproductCofiberGeometry.collapse X Y

/-- The complete original Q inclusion/collapse word retains the same counit and original right projection. -/
theorem inclusion_collapse :
    inclusion (B := B) (arrow X Y) ≫ collapse X Y =
      ε.app (X ⨿ Y) ≫ coprod.desc (Diagrams.toZero X ≫ Diagrams.zeroTo Y) (𝟙 Y) := by
  let a : Q.obj (X ⨿ Y) ⟶ (cofiber (B := B)).obj (arrow X Y) := inclusion (B := B) (arrow X Y)
  let b := toConeCofiber (B := B) X Y
  let c := CoproductCofiberGeometry.collapse (B := B) X Y
  have h := toConeCofiber_target (B := B) X Y
  exact (Category.assoc a b c).symm.trans
    ((congrArg (fun f => f ≫ c) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => ε.app (X ⨿ Y) ≫ f) (CoproductCofiberGeometry.target_collapse X Y))))

private theorem coneCollapseWeak (Z : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((OriginalICone.cone (B := B)).obj Z)) := by
  have h : OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
      ((OriginalICone.cone (B := B)).obj Z) = (OriginalICone.contraction (B := B)).app Z :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration Z).2

/-- The same original Q-cofiber comparison is level weak for cofibrant original summands. -/
theorem toConeCofiber_weak [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (toConeCofiber (B := B) X Y) := by
  let _ : IsCofibrant (X ⨿ Y) := isCofibrant_of_cofibration (coprod.inl : X ⟶ X ⨿ Y)
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement X
  let _ : IsCofibrant (Q.obj (X ⨿ Y)) := Replacement.isCofibrant_cofibrantReplacement (X ⨿ Y)
  let _ : IsCofibrant (Q.mapArrow.obj (arrow X Y)).left :=
    Replacement.isCofibrant_cofibrantReplacement X
  let _ : IsCofibrant (Q.mapArrow.obj (arrow X Y)).right :=
    Replacement.isCofibrant_cofibrantReplacement (X ⨿ Y)
  let _ : IsCofibrant (arrow X Y).left := inferInstanceAs (IsCofibrant X)
  let _ : IsCofibrant (arrow X Y).right := inferInstanceAs (IsCofibrant (X ⨿ Y))
  let _ : Cofibration ((OriginalICone.inclusion (B := B)).app (Q.obj X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration _)
  let _ : Cofibration ((OriginalICone.inclusion (B := B)).app X) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration _)
  let _ : Cofibration ((OriginalICone.inclusion (B := B)).app (Q.mapArrow.obj (arrow X Y)).left) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration _)
  let _ : Cofibration ((OriginalICone.inclusion (B := B)).app (arrow X Y).left) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration _)
  let _ : WeakEquivalence (ε.app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations X).2
  let _ : WeakEquivalence (ε.app (X ⨿ Y)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (X ⨿ Y)).2
  let _ : WeakEquivalence (counitArrow X Y).left :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations X).2
  let _ : WeakEquivalence (counitArrow X Y).right :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (X ⨿ Y)).2
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (OrdinaryHoChosenFiberCofiberComparison.chosenCofiberMap_weak
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
      (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
      (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
      (counitArrow X Y) (coneCollapseWeak (Q.obj X)) (coneCollapseWeak X))

/-- The whole original Q cofiber collapse to the right summand is level weak. -/
theorem collapse_weak [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (collapse (B := B) X Y) := by
  let _ : WeakEquivalence (toConeCofiber (B := B) X Y) := toConeCofiber_weak (B := B) X Y
  let _ : WeakEquivalence (CoproductCofiberGeometry.collapse (B := B) X Y) :=
    CoproductCofiberGeometry.collapse_weak (B := B) X Y
  exact inferInstanceAs
    (WeakEquivalence (toConeCofiber (B := B) X Y ≫ CoproductCofiberGeometry.collapse (B := B) X Y))

end PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductQCofiberGeometry
