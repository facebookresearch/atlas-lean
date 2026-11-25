/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CompactSupportComparison

@[expose] public section

/-! # Tests for compact-support Betti cohomology, Verdier duality data and
proper functoriality -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.CompactSupportBetti
open MathlibExt.AlgebraicGeometry.VerdierBetti
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open MathlibExt.AlgebraicGeometry.CompactSupportComparison

namespace MathlibExtTest.AlgebraicGeometry.CompactSupportBetti

attribute [local instance] HasDerivedCategory.standard

/-- The zero section has empty support. -/
example (Z : TopCat.{0}) (F : RationalSheaf Z) : germSupport F 0 = ∅ := by
  ext x
  simp [germSupport]

/-- On a compact space every global section has compact support. -/
example (Z : TopCat.{0}) [CompactSpace Z] (F : RationalSheaf Z) (s : GlobalSections F) :
    s ∈ compactSections F :=
  show IsCompact _ from isClosed_closure.isCompact

/-- A sheaf morphism acts on compactly supported sections through global
sections. -/
example {Z : TopCat.{0}} {F G : RationalSheaf Z} (a : F ⟶ G) (s : compactSections F) :
    (compactSectionsMap a s).1 = a.hom.app (op ⊤) s.1 :=
  rfl

/-- Compactly supported sections form an additive functor. -/
example (Z : TopCat.{0}) : (sections Z).Additive := inferInstance

/-- Inverse image along a map from a compact space preserves compact supports. -/
example {Z W : TopCat.{0}} [CompactSpace Z] (f : Z ⟶ W) : SectionSupport f :=
  ⟨fun _ _ => isClosed_closure.isCompact⟩

/-- The shift adjunction identifies Borel–Moore classes with maps into the
dualizing complex. -/
example (Z : TopCat.{0}) (D : DualizingComplex Z) (n : ℤ) (a : BorelMoore Z D n) :
    (bmAdjointEquiv Z D n).symm (bmAdjoint Z D n a) = a :=
  (bmAdjointEquiv Z D n).symm_apply_apply a

/-- Borel–Moore homology is the rational dual of compactly supported
cohomology. -/
example (Z : TopCat.{0}) (D : DualizingComplex Z) (n : ℕ) :
    BorelMoore Z D (n : ℤ) ≃ₗ[ℚ] DualCohomology Z n :=
  derivedHomCompactSupportComparison Z D n

/-- The rational coefficients are injective rational vector spaces. -/
example : Injective (ModuleCat.of ℚ ℚ) := inferInstance

/-- A purity isomorphism gives the fundamental class and the trace. -/
example (Z : TopCat.{0}) (D : DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (MathlibExt.AlgebraicGeometry.BettiRealization.rationalUnit Z)⟦(2 * d : ℤ)⟧) :
    BorelMoore Z D (2 * d) :=
  fundamentalClass Z D d e

example (Z : TopCat.{0}) (D : DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (MathlibExt.AlgebraicGeometry.BettiRealization.rationalUnit Z)⟦(2 * d : ℤ)⟧) :
    (derivedSections Z).obj ((unitPlus Z)⟦(2 * d : ℤ)⟧) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{0} ℚ) 0).obj (ModuleCat.of ℚ ℚ) :=
  topTrace Z D d e

/-- Proper pullback data are unique, so Borel–Moore pushforward does not depend
on the witness. -/
example {Z W : TopCat.{0}} {f : Z ⟶ W} (P Q : ProperPullback f) (DZ : DualizingComplex Z)
    (DW : DualizingComplex W) (n : ℤ) :
    borelMoorePushforward P DZ DW n = borelMoorePushforward Q DZ DW n := by
  rw [Subsingleton.elim P Q]

/-- Proper pullback data give Borel–Moore pushforward. -/
example {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback f) (DZ : DualizingComplex Z)
    (DW : DualizingComplex W) (n : ℤ) : BorelMoore Z DZ n →ₗ[ℚ] BorelMoore W DW n :=
  borelMoorePushforward P DZ DW n

end MathlibExtTest.AlgebraicGeometry.CompactSupportBetti

end
