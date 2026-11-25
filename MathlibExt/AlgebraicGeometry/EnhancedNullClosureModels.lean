/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels

/-!
# Native closure laws of the prescribed enhanced null envelope

The universal envelope is proved isomorphism closed and triangulated
inside the original native derived category. Its cone weak maps contain
all identities on the original bounded source. These are structural
properties of the already fixed null category used by native bifunctor
localization; no enhanced reconstruction assumption occurs.

Source: D'Agnolo--Kashiwara1311.2374v2, Section4.4. Native
triangulated object properties and weak maps are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0, Joël Riou.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EnhancedNullClosureModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ZeroObject
open BorderedRealSpaceModels BorderedIndDerivedModels CompactSupportIndSheaves
open IndSheafPushforwardModels IndSheafCoefficientModels IndSheafInverseImageModels EnhancedIndQuotientModels

variable (k : Type) [Field k] (M : TopCat.{0})
  [CompactSheafSource k (enhancedSpace M).ambient]

local instance closureAbelianPreadditive (X : TopCat.{0}) [CompactSheafSource k X] :
    Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

variable (P₀ : ObjectProperty (IndDerived k (enhancedSpace M).ambient))

instance nullEnvelope_isClosedUnderIsomorphisms :
    (nullEnvelope k M P₀).IsClosedUnderIsomorphisms where
  of_iso e h := by
    intro Q hQ hIso hPQ
    have := hIso
    exact Q.prop_of_iso e (h Q hQ hIso hPQ)

instance nullEnvelope_containsZero : (nullEnvelope k M P₀).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    intro Q hQ hIso _
    have := hQ
    have := hIso
    exact Q.prop_zero⟩

instance nullEnvelope_stableUnderShift : (nullEnvelope k M P₀).IsStableUnderShift ℤ where
  isStableUnderShiftBy a :=
    { le_shift := by
        intro K h Q hQ hIso hPQ
        have := hQ
        exact Q.le_shift a K (h Q hQ hIso hPQ) }

instance nullEnvelope_isTriangulatedClosed₂ : (nullEnvelope k M P₀).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ ↦ by
    intro Q hQ hIso hPQ
    have := hQ
    have := hIso
    exact Q.ext_of_isTriangulatedClosed₂ T hT (h₁ Q hQ hIso hPQ) (h₃ Q hQ hIso hPQ))

instance nullEnvelope_isTriangulated : (nullEnvelope k M P₀).IsTriangulated := by
  constructor

variable [CompactSheafSource k M] [CompactSheafSource k (boundarySpace (enhancedSpace M))]
  (P : CompactPushforwardSource k (boundaryInclusion (enhancedSpace M)))
  (D : IndPushforwardSource k (boundaryInclusion (enhancedSpace M)) P)
  [(indProperImage k (boundaryInclusion (enhancedSpace M)) P D).Additive]
  (H : DerivedIndPushforwardSource k (boundaryInclusion (enhancedSpace M)) P D)
  (S : OrdinaryIndSource k (enhancedSpace M).ambient)
  (I : IndInverseImageSource k (baseProjection M) S)
  [(indInverseImage k (baseProjection M) S I).Additive]
  (E : ExactIndInverseImageSource k (baseProjection M) S I)

instance enhancedNull_isClosedUnderIsomorphisms :
    (enhancedNull k M P D H S I E).IsClosedUnderIsomorphisms :=
  inferInstanceAs ((nullEnvelope k M (enhancedNullGenerators k M P D H S I E)).IsClosedUnderIsomorphisms)

instance enhancedNull_isTriangulated : (enhancedNull k M P D H S I E).IsTriangulated :=
  inferInstanceAs ((nullEnvelope k M (enhancedNullGenerators k M P D H S I E)).IsTriangulated)

instance enhancedWeak_containsIdentities : (enhancedWeak k M P D H S I E).ContainsIdentities :=
  inferInstanceAs (((enhancedNull k M P D H S I E).trW.inverseImage
    (IsBounded k (enhancedSpace M).ambient).ι).ContainsIdentities)

end MathlibExt.AlgebraicGeometry.EnhancedNullClosureModels
