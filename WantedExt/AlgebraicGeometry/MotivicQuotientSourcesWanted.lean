/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicAffineQuotientModels
public import MathlibExt.AlgebraicGeometry.MotivicBundleModels
public import MathlibExt.AlgebraicGeometry.MotivicCofiberComparisons

/-!
# Actual affine-cycle, bundle and cofiber construction requests

The source targets fix the native cycle cokernel, every coefficient and
scheme/simplex section, the relative bundle total space and zero section,
and the actual mapping-cone descent. Motivic affine/Tate comparison and
Thom isomorphism are separate conclusions, and are not inputs here.

Sources: Voevodsky arXiv:math/0107109v1, Sections 2, 4 and 5;
Mazza--Voevodsky--Weibel, Lecture 14; native Stacks/Mathlib constructions.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicQuotientSourcesWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open PointedMotivicModels ReducedMotivicCohomologyModels
open MotivicAffineQuotientModels MotivicBundleModels MotivicCofiberComparisons

def_wanted module_sections (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (Q : PointedSimplicialModuleFunctor k) : ModuleSectionSystem Q

def_wanted bundle_geometry (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (X : SmoothScheme k) (M : X.scheme.left.Modules) (d : ℕ)
    (hM : AlgebraicBundleGeometry.IsBundle M d) : BundleGeometry X M d

def_wanted reduced_cofiber (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (F : ReducedFreeNisSystem k) (X Y : PointedSpaces (k := k)) (a : X ⟶ Y)
    (ha : ∀ U, Mono (a.right.app U)) : CofiberChainSource F a

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {A : StandardSchemes P}
  {R : RepresentableSystem D G}
  (N : EffectiveMotivicComplexModels.NisTensorSystem k)
  (Q : PointedSimplicialModuleFunctor k) (E : ExternalSystem P)
  (M : ModuleSectionSystem Q)

def_wanted affine_cycle_product :
    AffineCycleProduct (D := D) (G := G) (P := P) (A := A) (R := R) N Q E M

end WantedExt.AlgebraicGeometry.MotivicQuotientSourcesWanted
