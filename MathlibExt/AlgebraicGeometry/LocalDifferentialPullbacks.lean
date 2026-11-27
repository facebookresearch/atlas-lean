/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Actual local Kähler differentials and normalized pullback maps

The differential of a regular function is the native universal derivation,
transported through the native first exterior-power isomorphism and the
actual sheafification unit. A pullback map is fixed on every such local
differential, using the literal scheme appLE map and module pullback unit.
Its maps on point fibres are computed from native pullbackComp and the
same sheaf morphism; they cannot be supplied independently.

Universal Kähler functoriality and sheaf/module pullback are completed
source integration, not new Wanted constructions. Source:
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Topology/Sheaves/Modules/Differentials.lean (Apache 2.0),
and Mathlib ModuleCat/Differentials/Presheaf.lean.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
open MathlibExt.AlgebraicGeometry.GenericSectionMaps

variable {k : Type} [CommRing k] (X : Over (Spec (.of k)))

/-- Literal first-exterior-power and sheafification map on the actual differential module. -/
def firstExteriorSection (U : X.left.Opens) :
    (differentials k X).obj (op U) →+ Γ(forms k X 1,U) :=
  let P := formsPresheaf k X 1
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.left.ringCatSheaf.obj)).unit.app P
  let e := (PresheafOfModules.extPowSections 1 (differentials k X) (op U)).symm
  let e₁ := (exteriorPower.oneEquiv Γ(X.left,U) ((differentials k X).obj (op U))).symm
  ((η.app (op U)).hom.toAddMonoidHom.comp e.toAddMonoidHom).comp e₁.toAddMonoidHom

/-- Actual additive differential into the existing sheaf of algebraic one-forms. -/
def differential (U : X.left.Opens) : Γ(X.left,U) →+ Γ(forms k X 1,U) :=
  (firstExteriorSection X U).comp
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
      (scalarMap k X)).d

theorem differential_zero (U : X.left.Opens) : differential X U 0 = 0 :=
  (differential X U).map_zero

theorem differential_add (U : X.left.Opens) (a b : Γ(X.left,U)) :
    differential X U (a+b) = differential X U a + differential X U b :=
  (differential X U).map_add a b

theorem differential_scalar (U : X.left.Opens) (a : k) :
    differential X U ((scalarMap k X).app (op U) a) = 0 := by
  have h := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (scalarMap k X)).d_app (X := op U) a
  exact (congrArg (firstExteriorSection X U) h).trans (firstExteriorSection X U).map_zero

/-- A pullback map on 1-forms along a morphism $f : Y \to X$ of $k$-schemes, for a commutative ring
$k$: a map $f^*\Omega^1_{X/k} \to \Omega^1_{Y/k}$ of sheaves of $\mathcal{O}_Y$-modules (on the
sheaves of algebraic 1-forms `forms k X 1` and `forms k Y 1`) that sends the pullback of $da$ to
$d(f^\sharp a)$ for all opens $U \subseteq X$ and $W \subseteq f^{-1}(U)$ and every
$a \in \mathcal{O}_X(U)$, where $f^\sharp a \in \mathcal{O}_Y(W)$ is the pulled-back function. -/
structure PullbackDifferential {Y : Over (Spec (.of k))} (f : Y ⟶ X) where
  map : (Scheme.Modules.pullback f.left).obj (forms k X 1) ⟶ forms k Y 1
  normalized : ∀ (U : X.left.Opens) (W : Y.left.Opens) (h : W ≤ f.left ⁻¹ᵁ U)
    (a : Γ(X.left,U)),
    (map.app W) (localPullbackSection f.left (forms k X 1) U W h
      (differential X U a)) = differential Y W ((f.left.appLE U W h).hom a)

variable {X} {Y : Over (Spec (.of k))} {f : Y ⟶ X}

/-- The actual first cotangent-fibre module at any scheme-valued point. -/
abbrev CotangentFibre {Z : Scheme.{0}} (x : Z ⟶ X.left) :=
  Γ((Scheme.Modules.pullback x).obj (forms k X 1),⊤)

/-- Point-fibre pullback is computed from the same normalized sheaf map and native composition. -/
def fibreMap (P : PullbackDifferential X f) {Z : Scheme.{0}} (x : Z ⟶ Y.left) :
    CotangentFibre (X := X) (x ≫ f.left) →ₗ[Γ(Z,⊤)] CotangentFibre (X := Y) x :=
  (((Scheme.Modules.pullbackComp x f.left).inv.app (forms k X 1) ≫
    (Scheme.Modules.pullback x).map P.map).val.app (op ⊤)).hom

theorem fibreMap_zero (P : PullbackDifferential X f) {Z : Scheme.{0}} (x : Z ⟶ Y.left) :
    fibreMap P x 0 = 0 := (fibreMap P x).map_zero

theorem fibreMap_smul (P : PullbackDifferential X f) {Z : Scheme.{0}} (x : Z ⟶ Y.left)
    (a : Γ(Z,⊤)) (v : CotangentFibre (X := X) (x ≫ f.left)) :
    fibreMap P x (a • v) = a • fibreMap P x v := (fibreMap P x).map_smul a v

end MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
