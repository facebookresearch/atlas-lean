/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.POTCosections

/-!
# Cosection reduction and support of the computed POT virtual class

Both targets use the actual polynomial-presentation cone and actual
obstruction-module cosection. Cone reduction is set-theoretic: the literal
linear cosection equation is nilpotent in the atlas algebra, rather than an
incorrect scheme-theoretic vanishing claim. The localized class lives on the
literal coefficient-ideal degeneracy scheme and its closed push must equal
the already computed zero-section cone class.

Reference: Kiem--Li, *Localizing virtual cycles by cosections*,
https://arxiv.org/abs/1007.3085, Proposition 4.3, Corollary 4.6 and Theorem 5.1.
The completed generic Koszul resolution in AxiomMath/Stacks,
StacksFrontier/AlgebraicGeometry/Chow/ZeroSectionKoszul/KoszulCosectionResolution.lean,
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, is excluded. It resolves
ordinary closed immersions by regular Koszul sequences; it does not supply
this POT cone reduction or supported virtual-class refinement. Generic
localized Chern classes are also covered. Torus virtual localization is
residual scope beyond this affine cosection-support package.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.POTCosectionLocalizationWanted

open MathlibExt.AlgebraicGeometry.AffineConeAtlas
open MathlibExt.AlgebraicGeometry.GeometricChowOperators
open MathlibExt.AlgebraicGeometry.POTVirtualPullback
open MathlibExt.AlgebraicGeometry.POTCosections

variable {B : Type} [CommRing B] [Algebra ℂ B]
    (P : Algebra.Extension.{0} ℂ B) (F : ConePresentation P)

/-- The actual intrinsic cone is supported in the cosection kernel. -/
public theorem_wanted cosection_cone_reduction
    (_polynomial : ∃ n : ℕ, Nonempty (P.Ring ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ))
    (_pot : IsObstructionTheory F) (s : Cosection F) :
    IsNilpotent (atlasHom F (bundleEquation F s))

/-- A supported refinement of the fixed cone class in the actual degeneracy
Chow group, with its literal closed-push compatibility included. -/
public def_wanted localizedVirtualClass [IsNoetherianRing B]
    (_polynomial : ∃ n : ℕ, Nonempty (P.Ring ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ))
    (_pot : IsObstructionTheory F) (s : Cosection F)
    (D : ChowPullbackEquivalence (baseScheme (B := B)) (bundleScheme F)
      (bundleMap F) F.negativeRank)
    (J : ClosedCycleDescent (bundleScheme F) (coneMap F))
    (K : ClosedCycleDescent (baseScheme (B := B)) (degeneracyMap F s)) :
    LocalizedVirtualClass F s D J K

end WantedExt.AlgebraicGeometry.POTCosectionLocalizationWanted
