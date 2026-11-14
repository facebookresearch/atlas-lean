/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

@[expose] public noncomputable section

/-!
# Algebraic equivalence and normalized line-bundle families

The line bundles below are actual scheme module sheaves. Algebraic
triviality is witnessed by a line-bundle family over a connected smooth
curve joining the trivial bundle to the given bundle. The relative
condition tests every algebraically closed field-valued fiber. Products,
fiber inclusions, and pullbacks are Mathlib constructions.

References: S. Kleiman, *The Picard scheme*, FGA Explained, §9;
J. S. Milne, *Abelian Varieties*, §9.
-/

namespace MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- The ordinary sheaf tensor, obtained from the actual presheaf tensor
and sheafification. -/
def moduleTensor (X : Scheme.{u}) (L M : X.Modules) : X.Modules :=
  let P := PresheafOfModulesOfCommRing.{u} X.sheaf.obj
  let U := SheafOfModules.forget X.ringCatSheaf
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((curriedTensor P).obj (U.obj L) |>.obj (U.obj M))

/-- Inclusion of a fiber over a rational point in a product. -/
def pointSection {k : Type u} [Field k]
    (A C : Over (Spec (.of k))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    A ⟶ prod A C :=
  prod.lift (𝟙 A) (toUnit A ≫ p)

/-- Algebraic triviality witnessed by an actual connected smooth curve family. -/
def IsAlgebraicallyTrivial {k : Type u} [Field k]
    (A : Over (Spec (.of k))) (L : A.left.Modules) : Prop :=
  ∃ (C : Over (Spec (.of k))) (_ : IsSeparated C.hom)
    (_ : LocallyOfFiniteType C.hom) (_ : QuasiCompact C.hom)
    (_ : SmoothOfRelativeDimension 1 C.hom) (_ : GeometricallyConnected C.hom)
    (p q : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (M : (prod A C).left.Modules), IsLineBundle M ∧
      Nonempty ((Scheme.Modules.pullback (pointSection A C p).left).obj M ≅
        structureModule A.left) ∧
      Nonempty ((Scheme.Modules.pullback (pointSection A C q).left).obj M ≅ L)

/-- Every geometric fiber of a family is algebraically trivial. -/
def IsFibrewiseAlgebraicallyTrivial {X S : Scheme.{u}}
    (π : X ⟶ S) (L : X.Modules) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
    IsAlgebraicallyTrivial (Over.mk (pullback.snd π p))
      ((Scheme.Modules.pullback (pullback.fst π p)).obj L)

/-- The zero section of an abelian scheme after forming a product. -/
def zeroSectionAt {k : Type u} [Field k]
    (A T : Over (Spec (.of k))) [GrpObj A] : T ⟶ prod A T :=
  prod.lift (toUnit T ≫ η[A]) (𝟙 T)

/-- Normalization means trivial restriction along the actual zero section. -/
def IsNormalizedAtZero {k : Type u} [Field k]
    (A T : Over (Spec (.of k))) [GrpObj A]
    (L : (prod A T).left.Modules) : Prop :=
  Nonempty ((Scheme.Modules.pullback (zeroSectionAt A T).left).obj L ≅
    structureModule T.left)

/-- Pull a Poincaré family back along an actual parameter morphism. -/
def familyPullback {k : Type u} [Field k]
    (A D T : Over (Spec (.of k))) (P : (prod A D).left.Modules) (f : T ⟶ D) :
    (prod A T).left.Modules :=
  (Scheme.Modules.pullback (prod.map (𝟙 A) f).left).obj P

/-- A dual abelian variety with its normalized universal Picard-zero family. -/
structure DualAbelianVarietyModel {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] where
  /-- The represented dual, as a genuine scheme over the field. -/
  dual : Over (Spec (.of k))
  /-- Its commutative group structure. -/
  [group : GrpObj dual]
  [commutative : IsCommMonObj dual]
  [proper : IsProper dual.hom]
  [smooth : Smooth dual.hom]
  [connected : GeometricallyConnected dual.hom]
  /-- The universal module on the actual relative product. -/
  P : (prod A dual).left.Modules
  /-- The universal module is a line bundle. -/
  lineBundle : IsLineBundle P
  /-- It is normalized along the zero of the original variety. -/
  normalized : IsNormalizedAtZero A dual P
  /-- The origin of the dual parametrizes the trivial line bundle. -/
  normalizedDual :
    Nonempty ((Scheme.Modules.pullback (pointSection A dual η[dual]).left).obj P ≅
      structureModule A.left)
  /-- Its fibers belong to Picard zero. -/
  algebraicallyTrivial :
    IsFibrewiseAlgebraicallyTrivial (prod.snd : prod A dual ⟶ dual).left P
  /-- Addition in the dual is tensor product of the represented families. -/
  addition : ∀ (T : Over (Spec (.of k))) (f g : T ⟶ dual),
    Nonempty
      (familyPullback A dual T P
        (CartesianMonoidalCategory.lift f g ≫ μ[dual]) ≅
        moduleTensor (prod A T).left
          (familyPullback A dual T P f) (familyPullback A dual T P g))
  /-- Every normalized Picard-zero family is uniquely a pullback of this one. -/
  universal : ∀ (T : Over (Spec (.of k))) (L : (prod A T).left.Modules),
    IsLineBundle L → IsNormalizedAtZero A T L →
    IsFibrewiseAlgebraicallyTrivial (prod.snd : prod A T ⟶ T).left L →
      ∃! f : T ⟶ dual, Nonempty (familyPullback A dual T P f ≅ L)

end MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
