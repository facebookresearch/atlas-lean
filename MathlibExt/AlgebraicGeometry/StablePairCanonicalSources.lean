/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairFourierMukaiAtiyah
public import MathlibExt.AlgebraicGeometry.StablePairFamilies
public import MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The actual canonical-module source for stable-pair Serre duality

The canonical module is H⁻³ of the actual proper QCoh right adjoint
applied to the structure module. Its concentrated comparison is fixed
by the identity on that homology module. The relative canonical map
is its native pullback followed by the actual proper base-change mate.
Thus the relative trace has no freely selected canonical sheaf or
functional.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5, (2.13);
Stacks 0A9Y; the source-normalized proper references imported above.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairCanonicalSources

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open FourierMukai CoherentCurveLinearSeries StablePairFamilies
open QuasicoherentDualityReferences ModuleDerivedSquares StablePairFourierMukaiAtiyah
attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}]

/-- The generic smooth-proper comparison is fixed by its identity on H⁻³. -/
structure CanonicalModel {X : Over (Spec (.of ℂ))} (P : ProperReference X.hom) where
  map : (DerivedCategory.singleFunctor X.left.Modules (-3)).obj
    (properCanonicalModule P 3) ⟶ properDuality P
  [iso : IsIso map]
  normalized : (DerivedCategory.homologyFunctor X.left.Modules (-3)).map map =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.left.Modules (-3)).hom.app
      (properCanonicalModule P 3)

attribute [instance] CanonicalModel.iso

variable (X P : Over (Spec (.of ℂ))) (PX : ProperReference X.hom)

/-- The actual relative canonical module pulled back from X. -/
@[implicit_reducible]
def omegaModule : (total X P).Modules :=
  (Scheme.Modules.pullback (pullback.fst X.hom P.hom)).obj (properCanonicalModule PX 3)

/-- The native degree-zero representative of the relative canonical line. -/
@[implicit_reducible]
def omegaComplex : Cochains (total X P) :=
  (CochainComplex.singleFunctor (total X P).Modules 0).obj (omegaModule X P PX)

/-- The native shift comparison to the canonical module in degree -3. -/
def canonicalModelMap (C : CanonicalModel PX) :
    DerivedCategory.Q.obj
      (((CochainComplex.singleFunctor X.left.Modules 0).obj
        (properCanonicalModule PX 3))⟦(3 : ℤ)⟧) ⟶ properDuality PX :=
  (DerivedCategory.Q.commShiftIso (3 : ℤ)).hom.app
      ((CochainComplex.singleFunctor X.left.Modules 0).obj (properCanonicalModule PX 3)) ≫
    ((DerivedCategory.singleFunctors X.left.Modules).shiftIso 3 (-3) 0 (by omega)).hom.app
      (properCanonicalModule PX 3) ≫ C.map

/-- The relative canonical comparison is the actual normalized proper base-change construction. -/
def relativeCanonicalMap (PP : ProperReference (projection X P))
    (C : CanonicalModel PX)
    (AF : PullPushAdjunction X.hom) (AF' : PullPushAdjunction (projection X P))
    (A : PullbackPasting (projection X P) P.hom)
    (B : PullbackPasting (pullback.fst X.hom P.hom) X.hom) (U : UnitPullback P.hom)
    (hL : quasicoherent (total X P)
      ((derivedPullback (pullback.fst X.hom P.hom)).obj (properDuality PX)))
    (hBase : IsIso (ModuleDerivedSquares.baseChangeMap (pullback.fst X.hom P.hom)
      (projection X P) X.hom P.hom pullback.condition AF AF' A B (properDuality PX)))
    (hPull : IsIso (pullbackCounit (pullback.fst X.hom P.hom)
      (((CochainComplex.singleFunctor X.left.Modules 0).obj
        (properCanonicalModule PX 3))⟦(3 : ℤ)⟧))) :
    DerivedCategory.Q.obj ((omegaComplex X P PX)⟦(3 : ℤ)⟧) ⟶ properDuality PP := by
  letI := hPull
  exact DerivedCategory.Q.map
      (((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pullback (pullback.fst X.hom P.hom)) (.up ℤ) 0).inv.app
          (properCanonicalModule PX 3))⟦(3 : ℤ)⟧') ≫
    DerivedCategory.Q.map
      (((cochainPullback (pullback.fst X.hom P.hom)).commShiftIso (3 : ℤ)).inv.app
        ((CochainComplex.singleFunctor X.left.Modules 0).obj (properCanonicalModule PX 3))) ≫
    inv (pullbackCounit (pullback.fst X.hom P.hom)
      (((CochainComplex.singleFunctor X.left.Modules 0).obj
        (properCanonicalModule PX 3))⟦(3 : ℤ)⟧)) ≫
    (derivedPullback (pullback.fst X.hom P.hom)).map (canonicalModelMap X PX C) ≫
      properBaseChange (pullback.fst X.hom P.hom) (projection X P) X.hom P.hom
        pullback.condition PX PP AF AF' A B U hL hBase

end MathlibExt.AlgebraicGeometry.StablePairCanonicalSources
