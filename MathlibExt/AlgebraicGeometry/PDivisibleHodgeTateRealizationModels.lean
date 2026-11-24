/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests
public import MathlibExt.AlgebraicGeometry.PDivisibleFormalCartierCotangentModels

/-!
# Original Tate points, integral finite characters and formal Hodge--Tate realization

Each integral finite projection is the actual O_C scheme point whose
generic image is the displayed projection of the original native Tate
module. All p-power divisions and additions use the original group maps.
Finite dlog is then the actual Cartier-character dlog in I/I², and the
formal Hodge--Tate map is fixed by every actual finite cotangent projection.

Rational scalar extension uses the original inclusion O_C to C and the
native module scalar-extension functors, normalized on every pure tensor.
C may be any algebraically closed complete p-adic extension, including
non-discretely-valued and non-spherically-complete fields.

Source: Scholze--Weinstein, arXiv:1211.6357v2, recalled Hodge--Tate
sequence in Section 1 and Section 5.1; Tate, p-divisible groups (1967).
Integral finite-point extension and formal comparison remain construction
requests, separately from the completed generic Tate inverse limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleHodgeTateRealizationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AlgebraicallyClosedPadicTests PDivisibleGroupSchemes
open PDivisibleCartierTowerModels PDivisibleLieModels
open PDivisibleFormalCartierCotangentModels
open MathlibExt.Algebra.Module.Torsion
open scoped _root_.CategoryTheory.MonObj

variable (p : ℕ) [Fact p.Prime] (C : FieldTest p)
  (G : PDivisibleGroup (IntegralScheme p C) p)

/-- The actual geometric Tate module on Spec C over the original O_C. -/
abbrev Tate := PDivisibleGeometricTateModels.GeometricTate p (IntegralScheme p C) G
  (genericTest p C)

/-- The actual generic-to-integral base arrow, induced by O_C to C. -/
def genericToBase : genericTest p C ⟶ FiniteCartierCharacterModels.BaseTest (integers p C) :=
  Over.homMk (genericTest p C).hom (by
    change (genericTest p C).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (integers p C) (integers p C))) =
        (genericTest p C).hom
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

/-- An integral point whose original finite inclusion is the displayed native Tate projection. -/
def IntegralProjection (n : ℕ) (x : Tate p C G) :=
  {y : FiniteCartierCharacterModels.BaseTest (integers p C) ⟶ G.levels.obj n //
    ((PDivisibleGeometricTateModels.finiteInclusion p (IntegralScheme p C) G n).app
      (op (genericTest p C))).hom (Additive.ofMul (genericToBase p C ≫ y)) =
      (PDivisibleGeometricTateModels.projection p (IntegralScheme p C) G
        (genericTest p C) n x).val}

/-- Compatible integral finite projections of the original geometric Tate points. -/
structure IntegralProjectionSystem where
  point : ∀ (n : ℕ) (x : Tate p C G), IntegralProjection p C G n x
  division : ∀ (n m : ℕ) (x : Tate p C G),
    (point (n + m) x).val ≫ G.divide n m = (point m x).val
  zero : ∀ n : ℕ, (point n 0).val = 1
  addition : ∀ (n : ℕ) (x y : Tate p C G),
    (point n (x + y)).val = (point n x).val * (point n y).val

/-- Original Z_p coefficients in the actual generic field C. -/
def genericPadicScalars : PadicInt p →+* C.field :=
  (integerInclusion p C).comp (padicIntegerScalars p C)

/-- The genuine Tate twist, from the native p-power-root Tate module of C units. -/
abbrev TateRootUnits := ↥(_root_.TateModule p (Additive C.fieldˣ))

variable (D : CartierDualTower p (integers p C) G)
  (L : LieModel p (integers p C) D.group)

/-- The formal cotangent with its original Z_p scalar restriction. -/
abbrev IntegralTarget :=
  (ModuleCat.restrictScalars (padicIntegerScalars p C)).obj L.cotangent

/-- Actual rational scalar extension of the original geometric Tate module. -/
abbrev RationalTate :=
  (ModuleCat.extendScalars (genericPadicScalars p C)).obj
    (ModuleCat.of (PadicInt p) (Tate p C G))

/-- Actual scalar extension of the original formal cotangent O_C module. -/
abbrev RationalTarget :=
  (ModuleCat.extendScalars (integerInclusion p C)).obj L.cotangent

/-- The canonical comparison, fixed by every original finite character dlog. -/
structure HodgeTateMap (P : IntegralProjectionSystem p C G)
    (B : CotangentBridge p (integers p C) G D L) where
  map : Tate p C G →ₗ[PadicInt p] IntegralTarget p C G D L
  finite_normalization : ∀ (n : ℕ) (x : Tate p C G),
    B.projection n (map x) =
      geometricFiniteDlog p (integers p C) G n (Additive.ofMul (P.point n x).val)
  rational : RationalTate p C G →ₗ[C.field] RationalTarget p C G D L
  pure_normalization : ∀ (c : C.field) (x : Tate p C G),
    rational (c • (show RationalTate p C G from
      ((ModuleCat.extendRestrictScalarsAdj (genericPadicScalars p C)).unit.app
        (ModuleCat.of (PadicInt p) (Tate p C G))) x)) =
    c • (show RationalTarget p C G D L from
      ((ModuleCat.extendRestrictScalarsAdj (integerInclusion p C)).unit.app L.cotangent) (map x))

end MathlibExt.AlgebraicGeometry.PDivisibleHodgeTateRealizationModels
