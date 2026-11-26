/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualCompactPushforwardSource
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Tests for actual compact pushforward source

A skyscraper sheaf on a point, with nonzero stalk, is compactly supported;
its pushforward along a constant map to the naturals is compactly supported
by the actual compact pushforward source.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.IndSheafSourceRequestsActualCompactPushforwardSource

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open WantedExt.AlgebraicGeometry.IndSheafSourceRequests

/-- Any sheaf on a compact space is compactly supported. -/
theorem isCompactSupported_of_compactSpace (k : Type) [Field k]
    (X : TopCat.{0}) [CompactSpace X] (F : OrdinarySheaf k X) :
    IsCompactSupported k X F := by
  change IsCompact (ordinarySupport k X F)
  unfold ordinarySupport
  exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (Set.subset_univ _)

open scoped Classical in
/-- Skyscraper sheaf at the point of `PUnit` with value `ℚ`. -/
def punitSkyscraper : OrdinarySheaf ℚ (TopCat.of PUnit) :=
  skyscraperSheaf (X := TopCat.of PUnit) (PUnit.unit : TopCat.of PUnit)
    (ModuleCat.of ℚ ℚ)

/-- The skyscraper sheaf on `PUnit` is compactly supported. -/
def punitSkyscraperCompact : CompactSheaf ℚ (TopCat.of PUnit) where
  obj := punitSkyscraper
  property := isCompactSupported_of_compactSpace ℚ _ punitSkyscraper

open scoped Classical in
/-- The stalk of the `PUnit` skyscraper at the point is nonzero. -/
theorem stalk_punitSkyscraper_ne_zero :
    ¬IsZero (punitSkyscraper.presheaf.stalk (PUnit.unit : TopCat.of PUnit)) := by
  have hA : ¬IsZero (ModuleCat.of ℚ ℚ) := by
    rw [ModuleCat.isZero_of_iff_subsingleton]
    exact not_subsingleton_iff_nontrivial.mpr inferInstance
  intro hstalk
  apply hA
  have e : punitSkyscraper.presheaf.stalk (PUnit.unit : TopCat.of PUnit) ≅
      ModuleCat.of ℚ ℚ :=
    skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit)
      (PUnit.unit : TopCat.of PUnit) (ModuleCat.of ℚ ℚ) specializes_rfl
  exact hstalk.of_iso e.symm

/-- The support of the `PUnit` skyscraper contains the point. -/
theorem mem_support_punitSkyscraper :
    (PUnit.unit : TopCat.of PUnit) ∈ ordinarySupport ℚ (TopCat.of PUnit) punitSkyscraper := by
  unfold ordinarySupport
  exact subset_closure stalk_punitSkyscraper_ne_zero

/-- Constant map from `PUnit` to `ℕ` at zero. -/
def punitToNat : TopCat.of PUnit ⟶ TopCat.of ℕ :=
  TopCat.ofHom ⟨fun _ => 0, continuous_const⟩

/-- Pushforward of the `PUnit` skyscraper to `ℕ` is compactly supported. -/
theorem pushforward_punitSkyscraper :
    IsCompactSupported ℚ (TopCat.of ℕ)
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) punitToNat).obj
        punitSkyscraperCompact.obj) :=
  (actual_compact_pushforward_source ℚ _ _ punitToNat).compact punitSkyscraperCompact

end MathlibExtTest.AlgebraicGeometry.IndSheafSourceRequestsActualCompactPushforwardSource
