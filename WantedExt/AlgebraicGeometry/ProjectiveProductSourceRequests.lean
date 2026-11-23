/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ProductDifferentialOperatorModels
public import MathlibExt.AlgebraicGeometry.NativeBetaInverseCompatibility

/-!
# Structural requests for the projective line, products and inverse images

The enhanced Riemann--Hilbert interfaces take the following structures as instances. Each is
requested here under its geometric hypotheses, so that those interfaces are conditional only on
these named requests (together with `actual_compact_sheaf_source`, `actual_ind_space_context`,
`actual_differential_beta_ring` and `actual_opposite_differential_beta_ring` in the companion
request files):

* the standard complex structure of the projective line, for which both affine coordinates
  `τ` and `ζ = 1/τ` are holomorphic. This determines the complex structure: an injective
  holomorphic map of Riemann surfaces is biholomorphic onto its open image;
* the product complex structure on `X × ℙ¹` for a complex manifold `X`, for which both projections
  are holomorphic (this again determines it);
* the braided monoidal structure of the ordinary sheaf inverse image, which commutes with the
  sheafified tensor product;
* the β-ring structure of a pulled-back ring sheaf, whose constants are the pulled-back constants.

The meromorphic coefficient algebra closure (`MeromorphicAlgebraSource`) is proved, not requested.

Source: D'Agnolo--Kashiwara, arXiv:1311.2374v2, §§2.2, 9.1 and 9.5 (the projective line, products
and inverse images used in the enhanced reconstruction); Kashiwara--Schapira, Sheaves on Manifolds,
§2.3 (inverse images and tensor products of sheaves).
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProjectiveProductSourceRequests

open _root_.CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry
open ProjectiveExponentialSectionModels ProductDifferentialOperatorModels
open CompactSupportIndSheaves NativeIndDifferentialContexts
open NativeBetaInverseCompatibility PulledBetaRingModels
open scoped Manifold ContDiff

/-- The standard complex structure of the projective line, with both affine coordinates
holomorphic. -/
public instance_wanted actual_projective_complex_source : ProjectiveComplexSource

/-- The product complex structure on `X × ℙ¹` for a complex manifold `X`, with both projections
holomorphic. -/
public def_wanted actual_product_complex_source (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
    [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X] :
  ProductComplexSource n X

/-- The ordinary inverse image of sheaves of complex vector spaces is braided monoidal for the
sheafified tensor products. -/
public def_wanted actual_ordinary_inverse_monoidal {X Y : TopCat.{0}} (f : Y ⟶ X)
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
    [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ X] [CompactSheafSource ℂ Y] [IndSpaceSource X] [IndSpaceSource Y] :
  OrdinaryInverseMonoidalSource f

/-- The pulled-back ring sheaf carries the β-ring structure whose constants are the pulled-back
constants. -/
public def_wanted actual_pulled_beta_ring {X Y : TopCat.{0}} (f : Y ⟶ X)
    (R : TopCat.Sheaf RingCat.{0} X)
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)] [CompactSheafSource ℂ X]
    [IndSpaceSource X] [BetaRingSource X R]
    [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)] [CompactSheafSource ℂ Y]
    [IndSpaceSource Y] :
  PulledBetaRingSource f R

end WantedExt.AlgebraicGeometry.ProjectiveProductSourceRequests
