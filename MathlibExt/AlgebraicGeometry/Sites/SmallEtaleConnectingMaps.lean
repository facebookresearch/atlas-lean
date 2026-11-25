/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-! # Canonical connecting maps on the original small étale site

Each map is the stock Yoneda product with the extension class of the same
actual short exact sequence. The common-universe sheaf category and its Ext
groups are constructed by `SmallEtaleCoefficientSections`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {X : Scheme.{u}}
  {S T : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}

/-- The fixed additive connecting map for the original short exact sequence. -/
def smallEtaleConnectingMap (hS : S.ShortExact) (n : ℕ) :
    Sheaf.H S.X₃ n →+ Sheaf.H S.X₁ (n + 1) :=
  Sheaf.H.δ hS n (n + 1) rfl

/-- Its value is the Yoneda composition with this same sequence's extension
class, with the original integral sheaf as the source. -/
theorem smallEtaleConnectingMap_apply (hS : S.ShortExact) (n : ℕ)
    (x : Sheaf.H S.X₃ n) :
    smallEtaleConnectingMap hS n x = x.comp hS.extClass rfl := rfl

/-- Every morphism of the original short exact sequences commutes with the
same chosen connecting maps and the actual cohomology maps. -/
theorem smallEtaleConnectingMap_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (α : S ⟶ T) (n : ℕ) (x : Sheaf.H S.X₃ n) :
    smallEtaleConnectingMap hT n (Sheaf.H.map α.τ₃ n x) =
      Sheaf.H.map α.τ₁ (n + 1) (smallEtaleConnectingMap hS n x) :=
  Sheaf.H.δ_naturality n (n + 1) rfl hS hT α x

/-- The complete canonical family, its actual Yoneda formula and naturality
on every original sequence, every degree and every sequence morphism. -/
theorem original_small_etale_connecting_maps (X : Scheme.{u}) :
    (∀ (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
      (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H S.X₃ n),
      smallEtaleConnectingMap hS n x = x.comp hS.extClass rfl) ∧
    ∀ (S T : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
      (hS : S.ShortExact) (hT : T.ShortExact) (α : S ⟶ T) (n : ℕ)
      (x : Sheaf.H S.X₃ n),
      smallEtaleConnectingMap hT n (Sheaf.H.map α.τ₃ n x) =
        Sheaf.H.map α.τ₁ (n + 1) (smallEtaleConnectingMap hS n x) := by
  exact ⟨fun _ hS n x => smallEtaleConnectingMap_apply hS n x,
    fun _ _ hS hT α n x => smallEtaleConnectingMap_naturality hS hT α n x⟩

end AlgebraicGeometry.Scheme.DerivedSections
