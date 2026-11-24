/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicSplitTorusModels
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import MathlibExt.AlgebraicGeometry.StablePairInternalHomMaps

/-!
# Actual tangent, normal and chamber eigensum geometry

Differential maps are fixed on the native sheafified Kähler wedge
generators on every open. Tangents are actual internal-Hom duals.
The normal is the cokernel of the dual of the original restriction map.
Its identification with moving weights retains the actual inclusion
and cokernel projection. Chambers and eigensums use the geometric
characters and the original cocharacter Laurent-coordinate map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TorusDifferentialGeometryModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels LinearizedLineBundles
  TorusFixedSchemeModels
open CoherentCurveLinearSeries

def formSymbol (R : Type) [CommRing R] (X : Over (Spec (.of R))) (U : X.left.Opens)
    (n : ℕ) (r : Fin n → Γ(X.left, U)) : (AlgebraicDifferentialSheaves.forms R X n).val.obj (op U)
      := by
  letI : CommRing ((X.left.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)) :=
    inferInstanceAs (CommRing (X.left.presheaf.obj (op U)))
  exact (((PresheafOfModules.sheafificationAdjunction (𝟙 X.left.ringCatSheaf.obj)).unit.app
    (AlgebraicDifferentialSheaves.formsPresheaf R X n)).app (op U)).hom
      (exteriorPower.ιMulti _ n (fun j => CommRingCat.KaehlerDifferential.d (r j)))

abbrev Omega (X : Over base) := AlgebraicDifferentialSheaves.forms ℂ X 1
abbrev Tangent (X : Over base) := BundleTrace.homSheaf X.left (Omega X) (structureModule X.left)

def pullModuleSection {X Y : Scheme.{0}} (f : Y ⟶ X) (E : X.Modules)
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (s : E.val.obj (op U)) :
    ((Scheme.Modules.pullback f).obj E).val.obj (op V) :=
  (((Scheme.Modules.pullback f).obj E).val.map (homOfLE h).op).hom
    (((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).val.app (op U)).hom) s)

/-- Evaluation is the original module morphism on the terminal slice object. -/
def homApply (X : Scheme.{0}) (E : X.Modules) (U : X.Opens)
    (v : (BundleTrace.homSheaf X E (structureModule X)).val.obj (op U))
    (s : E.val.obj (op U)) : Γ(X, U) := (v.app (op (Over.mk (𝟙 U)))).hom s

/-- Every exterior differential map belongs to the original scalar-preserving scheme square. -/
structure DifferentialSquareData (R S : Type) [CommRing R] [CommRing S]
    (X : Over (Spec (.of R))) (Y : Over (Spec (.of S)))
    (f : Y.left ⟶ X.left) (scalar : R →+* S) where
  square : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom scalar)
  map : ∀ n : ℕ, (Scheme.Modules.pullback f).obj (AlgebraicDifferentialSheaves.forms R X n) ⟶
    AlgebraicDifferentialSheaves.forms S Y n
  normalized : ∀ (U : X.left.Opens) (V : Y.left.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (r : Fin n → Γ(X.left, U)),
    (((map n).val.app (op V)).hom
      (pullModuleSection f (AlgebraicDifferentialSheaves.forms R X n) U V h (formSymbol R X U n r)))
        =
    formSymbol S Y V n (fun j => f.appLE U V h (r j))

/-- Finite-bundle dual pullback is fixed by actual local form evaluation. -/
structure DualPullbackData {X Y : Scheme.{0}} (f : Y ⟶ X) (E : X.Modules) where
  iso : (Scheme.Modules.pullback f).obj (BundleTrace.homSheaf X E (structureModule X)) ≅
    BundleTrace.homSheaf Y ((Scheme.Modules.pullback f).obj E) (structureModule Y)
  normalized : ∀ (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (v : (BundleTrace.homSheaf X E (structureModule X)).val.obj (op U)) (s : E.val.obj (op U)),
    homApply Y ((Scheme.Modules.pullback f).obj E) V
      (((iso.hom.val.app (op V)).hom)
        (pullModuleSection f (BundleTrace.homSheaf X E (structureModule X)) U V h v))
      (pullModuleSection f E U V h s) = f.appLE U V h (homApply X E U v s)

def relativeScheme {T : Over base} [GrpObj T] (M : TorusModel T) (X : Over base) :
    Over (Spec (.of (CoordinateRing M.rank))) :=
  Over.mk ((fst T X).left ≫ M.iso.hom.left)

/-- The natural torus action on forms is the actual relative action differential. -/
structure TorusFormsActionData {T : Over base} [GrpObj T] (M : TorusModel T)
    (X : Over base) [ModObj T X] where
  action : DifferentialSquareData ℂ (CoordinateRing M.rank) X (relativeScheme M X)
    γ[T,X].left (algebraMap ℂ (CoordinateRing M.rank))
  projection : DifferentialSquareData ℂ (CoordinateRing M.rank) X (relativeScheme M X)
    (snd T X).left (algebraMap ℂ (CoordinateRing M.rank))
  actionIso : ∀ n : ℕ, IsIso (action.map n)
  projectionIso : ∀ n : ℕ, IsIso (projection.map n)
  linearization : ∀ n : ℕ, Linearization T X (AlgebraicDifferentialSheaves.forms ℂ X n)
  normalized : ∀ n : ℕ, (linearization n).comparison.hom = action.map n ≫
    (@asIso _ _ _ _ (projection.map n) (projectionIso n)).inv

/-- Tangent transport is the dual of that same normalized cotangent transport. -/
structure TorusTangentActionData {T : Over base} [GrpObj T] (M : TorusModel T)
    (X : Over base) [ModObj T X] where
  forms : TorusFormsActionData M X
  actionDual : DualPullbackData γ[T,X].left (Omega X)
  projectionDual : DualPullbackData (snd T X).left (Omega X)
  linearization : Linearization T X (Tangent X)
  normalized : linearization.comparison.hom = actionDual.iso.hom ≫
    StablePairInternalHomMaps.precompose (forms.linearization 1).comparison.inv ≫
      projectionDual.iso.inv

/-- The torus acts literally trivially on its fixed scheme. -/
@[instance_reducible] def trivialGroupAction (T F : Over base) [GrpObj T] : ModObj T F where
  smul := snd T F
  one_smul := by simp [CartesianMonoidalCategory.leftUnitor_hom]
  mul_smul := by simp

structure CotangentRestrictionData {X F : Over base} (i : F ⟶ X) where
  differential : DifferentialSquareData ℂ ℂ X F i.left (RingHom.id ℂ)
  dual : DualPullbackData i.left (Omega X)

def CotangentRestrictionData.tangent {X F : Over base} {i : F ⟶ X} (P : CotangentRestrictionData i)
  :
    Tangent F ⟶ (Scheme.Modules.pullback i.left).obj (Tangent X) :=
  StablePairInternalHomMaps.precompose (P.differential.map 1) ≫ P.dual.iso.inv

/-- The normal is the actual cokernel of the derivative of the closed fixed inclusion. -/
def CotangentRestrictionData.normal {X F : Over base} {i : F ⟶ X} (P : CotangentRestrictionData i) :
    F.left.Modules := cokernel P.tangent

/-- No separately assigned normal bundle is accepted. -/
structure NormalGeometry {A X F : Over base} [GrpObj A] [ModObj A X]
    (M : TorusModel A) (i : F ⟶ X) (hi : FixedPoint A X i) where
  restriction : CotangentRestrictionData i
  tangent : TorusTangentActionData M X
  weights : WeightDecomposition tangent.linearization i hi
  moving : weights.moving ≅ restriction.normal
  normalized : weights.movingInclusion ≫ cokernel.π restriction.tangent = moving.hom

/-- Roots enumerate exactly the occurring nonzero normal weights, excluding rank-zero summands. -/
structure NormalRoots {A X F : Over base} [GrpObj A] [ModObj A X]
    {M : TorusModel A} {i : F ⟶ X} {hi : FixedPoint A X i} (N : NormalGeometry M i hi) where
  roots : RootCoordinates M
  index : Fin roots.count ≃ {j : Fin N.weights.count //
    ¬IsTrivialCharacter (N.weights.character j) ∧ 0 < N.weights.rank j}
  character : ∀ j : Fin roots.count, roots.character j = N.weights.character (index j).1

/-- A cocharacter's coordinates come from its actual pullback on every character coordinate. -/
structure ChamberCocharacter {A : Over base} [GrpObj A] {M : TorusModel A}
    {R : RootCoordinates M} (C : Chamber R) where
  map : Gm ⟶ A
  [hom : IsMonHom map]
  coordinate : Lattice M.rank
  normalized : ∀ j : Fin M.rank,
    map.left.appTop (M.iso.hom.left.appTop
      ((Scheme.ΓSpecIso (.of (CoordinateRing M.rank))).inv.hom
        (characterUnit M.rank (Pi.single j 1) : CoordinateRing M.rank))) =
      ((gmUnit ^ coordinate j : Γ(Gm.left, ⊤)ˣ) : Γ(Gm.left, ⊤))
  chamber : (fun j => (coordinate j : ℝ)) ∈ C.region
  paired : ∀ j : Fin R.count, IntegerCharacter (pairedCharacter (R.character j) map)
  pairing : ∀ j : Fin R.count, (paired j).weight = ∑ k, (R.coordinates j).exponent k * coordinate k

attribute [instance] ChamberCocharacter.hom

variable {A X F : Over base} [GrpObj A] [ModObj A X]
  {M : TorusModel A} {i : F ⟶ X} {hi : FixedPoint A X i} {N : NormalGeometry M i hi}
  (R : NormalRoots N) (C : Chamber R.roots) (L : ChamberCocharacter C)

/-- The negative bundle is the native biproduct of the actual chamber-negative eigensummands. -/
def negativeNormal : F.left.Modules := by
  classical
  letI := Fintype.ofFinite {j : Fin R.roots.count // (L.paired j).weight < 0}
  exact biproduct (fun j : {j : Fin R.roots.count // (L.paired j).weight < 0} =>
    N.weights.bundle (R.index j.1).1)

def positiveNormal : F.left.Modules := by
  classical
  letI := Fintype.ofFinite {j : Fin R.roots.count // 0 < (L.paired j).weight}
  exact biproduct (fun j : {j : Fin R.roots.count // 0 < (L.paired j).weight} =>
    N.weights.bundle (R.index j.1).1)

def negativeRank : ℕ := by
  classical
  exact ∑ j : Fin R.roots.count, if (L.paired j).weight < 0 then N.weights.rank (R.index j).1 else 0

def normalRank : ℕ := ∑ j : Fin R.roots.count, N.weights.rank (R.index j).1

end MathlibExt.AlgebraicGeometry.TorusDifferentialGeometryModels
