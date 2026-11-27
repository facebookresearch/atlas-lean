/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import MathlibExt.AlgebraicGeometry.SchemeModulesTensor

@[expose] public noncomputable section

/-!
# Algebraic equivalence and line-bundle families

The line bundles below are actual scheme module sheaves. Over an
algebraically closed field, algebraic triviality is witnessed by a
line-bundle family over a connected smooth curve joining the trivial bundle
to the given bundle. The relative condition tests every algebraically closed
field-valued fiber. Products,
fiber inclusions, and pullbacks are Mathlib constructions. The sheaf tensor
product and tensor powers are those of `SchemeModulesTensor`, re-exported
here.

References: S. Kleiman, *The Picard scheme*, FGA Explained, §9;
J. S. Milne, *Abelian Varieties*, §9.
-/

namespace MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

export _root_.MathlibExt.AlgebraicGeometry.SchemeModulesTensor (moduleTensor power)

universe u

/-- Inclusion of a fiber over a rational point in a product. -/
def pointSection {k : Type u} [Field k]
    (A C : Over (Spec (.of k))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    A ⟶ prod A C :=
  prod.lift (𝟙 A) (toUnit A ≫ p)

/-- Algebraic triviality over an algebraically closed field, witnessed by an actual
line-bundle family over a connected smooth curve joining the trivial bundle to `L`
at two rational points. (Over a field that is not algebraically closed, algebraic
equivalence allows geometric endpoints, so this predicate is only stated over
algebraically closed fields; families test it on geometric fibers.) -/
def IsAlgebraicallyTrivial {k : Type u} [Field k] [IsAlgClosed k]
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

/-- Pull a family on `A ×_S D` back along an actual parameter morphism `T ⟶ D`, over an
arbitrary base scheme `S`. -/
def familyPullback {S : Scheme.{u}}
    (A D T : Over S) (P : (prod A D).left.Modules) (f : T ⟶ D) :
    (prod A T).left.Modules :=
  (Scheme.Modules.pullback (prod.map (𝟙 A) f).left).obj P

end MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
