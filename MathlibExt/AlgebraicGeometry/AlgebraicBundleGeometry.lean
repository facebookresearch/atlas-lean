/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The universal-property interfaces follow AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Constructions/VectorBundleOfModule.lean
and StacksFrontier/AlgebraicGeometry/Chow/ProjectiveBundleFormula/Formula.lean,
licensed under Apache 2.0. Modification notice: expose only characterized
positive-rank bundle data, retaining actual Mathlib module pullbacks and
the canonical unit comparison in the section/quotient formulas. No global
relative-Proj or total-space existence proof is claimed by this interface.
-/

module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import MathlibExt.AlgebraicGeometry.PerverseSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-!
# Geometric bundle inputs with actual universal properties

The projective bundle represents invertible quotients of the given actual
sheaf of modules; the quotient compatibility is included in its uniqueness
condition. The total space of a line bundle represents actual pulled-back
sections, and its zero section is fixed by the zero section of that same
universal property. These are characterized input constructions already
available in the cited source, not arbitrary carriers or extra Betti laws.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

def pullbackUnit (X Y : Scheme.{0}) (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : (TopologicalSpace.Opens.map f.base).Final := by infer_instance
  letI := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

def pullbackSection {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnit X Y f).inv ≫ (Scheme.Modules.pullback f).map s

open MathlibExt.AlgebraicGeometry.PerverseSheaves

def IsBundle {X : Scheme.{0}} (E : X.Modules) (r : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin r))

def IsLine {X : Scheme.{0}} (L : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

def pulledQuotient {X T V : ComplexScheme} (E : X.left.Modules) (L : V.left.Modules)
    (p : V ⟶ X) (q : (Scheme.Modules.pullback p.left).obj E ⟶ L)
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) (M : T.left.Modules)
    (e : (Scheme.Modules.pullback g.left).obj L ≅ M) :
    (Scheme.Modules.pullback f.left).obj E ⟶ M :=
  (Scheme.Modules.pullbackCongr (congrArg (fun v : T ⟶ X => v.left) h).symm).hom.app E ≫
    (Scheme.Modules.pullbackComp g.left p.left).inv.app E ≫
      (Scheme.Modules.pullback g.left).map q ≫ e.hom

structure ProjectiveBundle (X : ComplexScheme) (dx r : ℕ) (E : X.left.Modules) where
  isBundle : IsBundle E (r + 1)
  total : ComplexScheme
  projection : total ⟶ X
  [variety : IsComplexVariety total]
  [proper : IsProper projection.left]
  [properTotal : IsProper total.hom]
  [smooth : SmoothOfRelativeDimension (dx + r) total.hom]
  [relativeSmooth : SmoothOfRelativeDimension r projection.left]
  tautological : total.left.Modules
  isLine : IsLine tautological
  quotient : (Scheme.Modules.pullback projection.left).obj E ⟶ tautological
  [epiQuotient : Epi quotient]
  universal : ∀ (T : ComplexScheme) (f : T ⟶ X) (M : T.left.Modules)
    (_hM : IsLine M) (q : (Scheme.Modules.pullback f.left).obj E ⟶ M) (_hq : Epi q),
    ∃! g : T ⟶ total, ∃ (h : g ≫ projection = f)
      (e : (Scheme.Modules.pullback g.left).obj tautological ≅ M),
      q = pulledQuotient E tautological projection quotient f g h M e

attribute [instance] ProjectiveBundle.variety ProjectiveBundle.proper ProjectiveBundle.properTotal
  ProjectiveBundle.smooth ProjectiveBundle.relativeSmooth ProjectiveBundle.epiQuotient

def pulledCompositeSection {X T V : ComplexScheme} (L : X.left.Modules)
    (p : V ⟶ X) (s : SheafOfModules.unit V.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback p.left).obj L)
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) :
    SheafOfModules.unit T.left.ringCatSheaf ⟶ (Scheme.Modules.pullback f.left).obj L :=
  pullbackSection g.left ((Scheme.Modules.pullback p.left).obj L) s ≫
    (Scheme.Modules.pullbackComp g.left p.left).hom.app L ≫
      (Scheme.Modules.pullbackCongr (congrArg (fun v : T ⟶ X => v.left) h)).hom.app L

structure LineTotalSpace (X : ComplexScheme) (dx : ℕ) (L : X.left.Modules) where
  isLine : IsLine L
  total : ComplexScheme
  projection : total ⟶ X
  [variety : IsComplexVariety total]
  [smooth : SmoothOfRelativeDimension (dx + 1) total.hom]
  universalSection : SheafOfModules.unit total.left.ringCatSheaf ⟶
    (Scheme.Modules.pullback projection.left).obj L
  universal : ∀ (T : ComplexScheme) (f : T ⟶ X)
    (s : SheafOfModules.unit T.left.ringCatSheaf ⟶ (Scheme.Modules.pullback f.left).obj L),
    ∃! g : T ⟶ total, ∃ h : g ≫ projection = f,
      s = pulledCompositeSection L projection universalSection f g h
  zero : X ⟶ total
  zero_projection : zero ≫ projection = 𝟙 X
  zero_section : pulledCompositeSection L projection universalSection (𝟙 X) zero zero_projection = 0
  [closedZero : IsClosedImmersion zero.left]

attribute [instance] LineTotalSpace.variety LineTotalSpace.smooth LineTotalSpace.closedZero

end MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
