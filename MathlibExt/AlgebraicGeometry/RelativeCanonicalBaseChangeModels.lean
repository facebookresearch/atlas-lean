/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
public import MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps

/-!
# Underived canonical-module base change without a whole-complex flatness assumption

For a sheaf concentrated in degree d, the actual derived pullback counit
is compared only in degree d. Right exactness identifies that cohomology
with the actual ordinary pullback; lower Tor terms may remain. The
canonical-module map then uses the fixed duality base-change arrow and
the fixed lowest-cohomology embedding.

This supplies maps needed to state Kollár compatibility on arbitrary
base changes without assuming the entire single-sheaf pullback complex
is already its underived pullback. Generic derived pullback and duality
comparisons are existing source integration.
References: Stacks Project, Tags 0A9Y/08IB; Kollár, Families of varieties
of general type, relative canonical sheaves and Kollár condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeCanonicalBaseChangeModels

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open FourierMukai RelativeReflexiveCanonicalPowers ModuleDerivedSquares
open QuasicoherentDualityReferences
open AlgebraicLineBundleFamilies LineBundleTaskContracts NormalizedModuleTensorMaps
open ModuleInternalHom

attribute [local instance] HasDerivedCategory.standard
variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}]

/-- The native cohomology counit in the single sheaf's own degree. -/
def singleHomologyCounit {X Y : Scheme.{0}} (p : X ⟶ Y) (M : Y.Modules) (d : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules d).obj
        ((derivedPullback p).obj ((DerivedCategory.singleFunctor Y.Modules d).obj M)) ⟶
      (Scheme.Modules.pullback p).obj M :=
  (DerivedCategory.homologyFunctor X.Modules d).map
    ((derivedPullbackCounit p).app ((CochainComplex.singleFunctor Y.Modules d).obj M)) ≫
    (DerivedCategory.homologyFunctor X.Modules d).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.pullback p) (.up ℤ) d).hom.app M)) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules d).hom.app
        ((Scheme.Modules.pullback p).obj M)

def canonicalModuleMap {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) (P : ProperReference f) (P' : ProperReference f')
    (AF : PullPushAdjunction f) (AF' : PullPushAdjunction f')
    (A : PullbackPasting f' g) (B : PullbackPasting p f) (U : UnitPullback g) (n : ℕ)
    (C : CanonicalEmbedding P n)
    (hL : quasicoherent X' ((derivedPullback p).obj (properDuality P)))
    (hbase : IsIso (baseChangeMap p f' f g comm AF AF' A B (properDuality P)))
    (hdegree : IsIso (singleHomologyCounit p (properCanonicalModule P n) (-(n : ℤ)))) :
    (Scheme.Modules.pullback p).obj (properCanonicalModule P n) ⟶ properCanonicalModule P' n :=
  inv (singleHomologyCounit p (properCanonicalModule P n) (-(n : ℤ))) ≫
    (DerivedCategory.homologyFunctor X'.Modules (-(n : ℤ))).map
      ((derivedPullback p).map C.map ≫
        properBaseChange p f' f g comm P P' AF AF' A B U hL hbase)

/-- The actual reflexive log power, twisted by the supplied geometric m-boundary module. -/
def logCanonicalPower {X Y : Scheme.{0}} {f : X ⟶ Y} (P : ProperReference f)
    (n m : ℕ) (boundary : X.Modules) : X.Modules :=
  BirationalDualityReferences.reflexivePower
    (moduleTensor X (power (properCanonicalModule P n) m) boundary) 1

/-- The untwisted degree-one log-module map uses the same canonical arrow
and the literal pulled-back boundary module. -/
def logCanonicalModuleMap {X' X : Scheme.{0}} (p : X' ⟶ X)
    (M : X.Modules) (N : X'.Modules)
    (α : (Scheme.Modules.pullback p).obj M ⟶ N) (boundary : X.Modules)
    (T : PullbackTensor p) :
    (Scheme.Modules.pullback p).obj (moduleTensor X M boundary) ⟶
      moduleTensor X' N ((Scheme.Modules.pullback p).obj boundary) :=
  (T.comparison M boundary).hom ≫ tensorMap α (𝟙 ((Scheme.Modules.pullback p).obj boundary))

end MathlibExt.AlgebraicGeometry.RelativeCanonicalBaseChangeModels
