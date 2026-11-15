/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass
public import MathlibExt.AlgebraicGeometry.POTVirtualPullback

/-!
# Intrinsic POT cone-atlas and virtual zero-section comparisons

The normal ring is the actual base-changed Rees algebra. The atlas includes
the dual kernel of the chosen degree-zero splitting, and its embedding into
the obstruction bundle is the literal cotangent/projected-differential map.
Its quotient groupoid uses actual E⁰-dual translations. Closedness and
translation stability make this the affine presentation of the intrinsic
cone map, rather than an arbitrarily named cone or virtual-class carrier.

The virtual zero-section operator and class are already computed from the
cone image cycle and actual cycle pullback/pushforward maps. The standing
descent/bijection proof inputs concern those fixed maps. The remaining
comparisons are intrinsic splitting and acyclic-POT compatibility; generic
chosen-closed-immersion virtual classes are already completed in Axiom:
https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Chow/BivariantLemmas/VirtualNormalBundleClassConstruction.lean

Reference: Behrend--Fantechi, *The intrinsic normal cone*, §§2, 4--5,
https://arxiv.org/abs/alg-geom/9601010. This packet gives affine quotient
presentations and zero-section pullbacks, not a new generic stackification.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffinePOTVirtualClassWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.AffineConeAtlas
open MathlibExt.AlgebraicGeometry.GeometricChowOperators
open MathlibExt.AlgebraicGeometry.POTVirtualPullback

variable {B : Type} [CommRing B] [Algebra ℂ B]
  (P : Algebra.Extension.{0} ℂ B) (F : ConePresentation P)

/-- The actual POT atlas embeds as a closed cone in the obstruction bundle. -/
public theorem_wanted cone_atlas_closed [IsNoetherianRing B]
    (_polynomial : ∃ n : ℕ, Nonempty (P.Ring ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ))
    (_pot : IsObstructionTheory F) : Function.Surjective (atlasHom F)

/-- Every actual degree-zero dual translation preserves the concrete atlas
image, giving its affine quotient-cone presentation. -/
public theorem_wanted cone_translation_stability [IsNoetherianRing B]
    (_polynomial : ∃ n : ℕ, Nonempty (P.Ring ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ))
    (_pot : IsObstructionTheory F) (C : Type) [CommRing C] [Algebra B C]
    (a : AtlasPoint F C) (t : (Fin F.zeroRank → B) →ₗ[B] C) :
    ∃ b : AtlasPoint F C, coordinates F C b = coordinates F C a + t ∘ₗ F.differential

/-- Changing the actual splitting preserves the literal closed cone ideal. -/
public theorem_wanted splitting_ideal_independence [IsNoetherianRing B]
    (_polynomial : ∃ n : ℕ, Nonempty (P.Ring ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ))
    (_pot : IsObstructionTheory F)
    (s : P.CotangentSpace →ₗ[B] (Fin F.zeroRank → B))
    (hs : F.zeroMap ∘ₗ s = LinearMap.id) :
    RingHom.ker (atlasHom F).toRingHom = RingHom.ker (atlasHom (changeSplitting F s hs)).toRingHom

/-- An actual acyclic stabilization of the POT presentation preserves the
computed virtual class, with no independently chosen class operator. -/
public theorem_wanted acyclic_virtual_class_independence [IsNoetherianRing B]
    (polynomial : ∃ n : ℕ, Nonempty (P.Ring ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ))
    (potF : IsObstructionTheory F) (G : ConePresentation P) (potG : IsObstructionTheory G)
    (c : ℕ) (μ : (Fin c → B) →ₗ[B] P.Cotangent)
    (a : AcyclicStabilization F G c μ)
    (DF : ChowPullbackEquivalence (baseScheme (B := B)) (bundleScheme F)
      (bundleMap F) F.negativeRank)
    (DG : ChowPullbackEquivalence (baseScheme (B := B)) (bundleScheme G)
      (bundleMap G) G.negativeRank)
    (JF : ClosedCycleDescent (bundleScheme F) (coneMap F))
    (JG : ClosedCycleDescent (bundleScheme G) (coneMap G)) :
    virtualClass F DF JF potF polynomial =
      gradedChowCast (baseScheme (B := B)) (by have := a.negativeRank; have := a.zeroRank; omega)
        (virtualClass G DG JG potG polynomial)

end WantedExt.AlgebraicGeometry.AffinePOTVirtualClassWanted
