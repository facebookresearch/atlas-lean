/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BorderedIndDerivedModels
public import MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels

/-!
# The actual enhanced quotient over the bordered real line

The source is the bounded derived Ind category of M times the native
two-point compactification. The null category is the smallest isomorphism
closed triangulated subcategory containing the actual closed-boundary
image and the actual inverse-image image of bounded Ind complexes on M.
The weak maps are exactly the maps whose native cones lie in that null
category. This presents the two successive source quotients in one
native localization; escaping nonzero Ind objects are retained.

Source: D'Agnolo--Kashiwara1311.2374v2, Definition3.2.6,
Definition4.4.1 and Lemma4.4.3. The latter identifies the enhanced null
objects with the actual pi-inverse-image image after the boundary quotient.
No restriction kernel or ind-stalk-zero surrogate occurs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open BorderedRealSpaceModels BorderedIndDerivedModels CompactSupportIndSheaves
open IndSheafPushforwardModels IndSheafCoefficientModels IndSheafInverseImageModels

/-- An ordinary topological space, with its complete specified interior. -/
def fullBordered (M : TopCat.{0}) : BorderedSpace := ⟨M, ⊤⟩

/-- The actual product of M with the bordered native real line. -/
def enhancedSpace (M : TopCat.{0}) : BorderedSpace := product (fullBordered M) infiniteReal

/-- The full ambient projection whose quotient induces the source pi inverse image. -/
def baseProjection (M : TopCat.{0}) : (enhancedSpace M).ambient ⟶ M :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- Compactness of the real compactification makes this ambient projection proper. -/
theorem baseProjection_proper (M : TopCat.{0}) : IsProperMap (baseProjection M) :=
  isProperMap_fst_of_compactSpace

variable (k : Type) [Field k] (M : TopCat.{0})
  [CompactSheafSource k M]
  [CompactSheafSource k (enhancedSpace M).ambient]
  [CompactSheafSource k (boundarySpace (enhancedSpace M))]

/-- Use the same abelian zero morphisms as the native derived quotient. -/
local instance enhancedAbelianPreadditive (Z : TopCat.{0}) [CompactSheafSource k Z] :
    Preadditive (IndSheaf k Z) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

variable
  (P : CompactPushforwardSource k (boundaryInclusion (enhancedSpace M)))
  (D : IndPushforwardSource k (boundaryInclusion (enhancedSpace M)) P)
  [(indProperImage k (boundaryInclusion (enhancedSpace M)) P D).Additive]
  (H : DerivedIndPushforwardSource k (boundaryInclusion (enhancedSpace M)) P D)
  (S : OrdinaryIndSource k (enhancedSpace M).ambient)
  (I : IndInverseImageSource k (baseProjection M) S)
  [(indInverseImage k (baseProjection M) S I).Additive]
  (E : ExactIndInverseImageSource k (baseProjection M) S I)

/-- Actual pi-inverse images of bounded complexes on the original base M. -/
def baseImage : ObjectProperty (IndDerived k (enhancedSpace M).ambient) := fun K =>
  ∃ F : BoundedIndDerived k M,
    Nonempty ((derivedIndInverseImage k (baseProjection M) S I E).obj F.obj ≅ K)

/-- The two exact source images before triangulated closure. -/
def enhancedNullGenerators : ObjectProperty (IndDerived k (enhancedSpace M).ambient) :=
  boundaryImage k (enhancedSpace M) P D H ⊔ baseImage k M S I E

/-- The smallest isomorphism closed triangulated envelope in the original native category. -/
def nullEnvelope (P₀ : ObjectProperty (IndDerived k (enhancedSpace M).ambient)) :
    ObjectProperty (IndDerived k (enhancedSpace M).ambient) := fun K =>
  ∀ Q : ObjectProperty (IndDerived k (enhancedSpace M).ambient),
    Q.IsTriangulated → Q.IsClosedUnderIsomorphisms → P₀ ≤ Q → Q K

omit [CompactSheafSource k M] [CompactSheafSource k (boundarySpace (enhancedSpace M))] in
/-- Every original null generator lies in its native triangulated envelope. -/
theorem nullEnvelope_contains (P₀ : ObjectProperty (IndDerived k (enhancedSpace M).ambient)) :
    P₀ ≤ nullEnvelope k M P₀ := by
  intro K hK Q _ _ hPQ
  exact hPQ K hK

omit [CompactSheafSource k M] [CompactSheafSource k (boundarySpace (enhancedSpace M))] in
/-- The envelope is contained in every isomorphism closed triangulated subcategory containing the generators. -/
theorem nullEnvelope_minimal (P₀ Q : ObjectProperty (IndDerived k (enhancedSpace M).ambient))
    (hQ : Q.IsTriangulated) (hIso : Q.IsClosedUnderIsomorphisms) (hPQ : P₀ ≤ Q) :
    nullEnvelope k M P₀ ≤ Q := by
  intro K hK
  exact hK Q hQ hIso hPQ

/-- The source enhanced null category retains both actual quotient steps. -/
def enhancedNull : ObjectProperty (IndDerived k (enhancedSpace M).ambient) :=
  nullEnvelope k M (enhancedNullGenerators k M P D H S I E)

/-- Native cone maps into that exact enhanced null category. -/
def enhancedWeak : MorphismProperty (BoundedIndDerived k (enhancedSpace M).ambient) :=
  fun _ _ f => (enhancedNull k M P D H S I E).trW f.hom

/-- The actual enhanced bounded Ind category is the fixed native localization. -/
abbrev EnhancedDerived := (enhancedWeak k M P D H S I E).Localization

/-- The source quotient sends every ambient bounded complex through its actual weak-map localization. -/
def enhancedQuotient :
    BoundedIndDerived k (enhancedSpace M).ambient ⥤ EnhancedDerived k M P D H S I E :=
  (enhancedWeak k M P D H S I E).Q

end MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels
