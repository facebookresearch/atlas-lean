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

/-!
# Connecting maps in small étale cohomology

Let X be a scheme in universe u and c = max(u, w), with w independent.
For an abelian sheaf F on the small étale site with coefficients in
AddCommGrpCat c, write Hⁿ(X, F) = Extⁿ(ℤ_X, F), where ℤ_X is the constant
integral sheaf. A short exact sequence
0 → F₁ → F₂ → F₃ → 0 has extension class [S] ∈ Ext¹(F₃, F₁).

The additive connecting map δ_S : Hⁿ(X, F₃) → Hⁿ⁺¹(X, F₁) is
δ_S(x) = [S] ∘ x, the Yoneda product in this order.
It is natural under morphisms of short exact sequences.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {X : Scheme.{u}}
  {S T : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}

/-- Let X be a scheme in universe u, c = max(u, w), and
0 → F₁ → F₂ → F₃ → 0 a short exact sequence of AddCommGrpCat c-valued
sheaves on its small étale site. For n ∈ ℕ, this is the additive map
δ_S : Hⁿ(X, F₃) → Hⁿ⁺¹(X, F₁), given by Yoneda composition with the
extension class [S] ∈ Ext¹(F₃, F₁). -/
def smallEtaleConnectingMap (hS : S.ShortExact) (n : ℕ) :
    Sheaf.H S.X₃ n →+ Sheaf.H S.X₁ (n + 1) :=
  Sheaf.H.δ hS n (n + 1) rfl

/-- For a short exact sequence S : 0 → F₁ → F₂ → F₃ → 0 of abelian
sheaves on the small étale site of a scheme X, with coefficients in
c = max(u, w), the degree n connecting map has value
δ_S(x) = [S] ∘ x for x ∈ Hⁿ(X, F₃) = Extⁿ(ℤ_X, F₃).
The extension class [S] is composed after x, producing Extⁿ⁺¹(ℤ_X, F₁). -/
theorem smallEtaleConnectingMap_apply (hS : S.ShortExact) (n : ℕ)
    (x : Sheaf.H S.X₃ n) :
    smallEtaleConnectingMap hS n x = x.comp hS.extClass rfl := rfl

/-- Let X be a scheme in universe u and let S, T be short exact
sequences of abelian sheaves with coefficients in c = max(u, w) on its
small étale site. For a sequence morphism α : S → T and x ∈ Hⁿ(X, S₃),
the connecting maps satisfy
δ_T(Hⁿ(α₃)(x)) = Hⁿ⁺¹(α₁)(δ_S(x)).
Both short-exactness hypotheses and all n ∈ ℕ are included. -/
theorem smallEtaleConnectingMap_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (α : S ⟶ T) (n : ℕ) (x : Sheaf.H S.X₃ n) :
    smallEtaleConnectingMap hT n (Sheaf.H.map α.τ₃ n x) =
      Sheaf.H.map α.τ₁ (n + 1) (smallEtaleConnectingMap hS n x) :=
  Sheaf.H.δ_naturality n (n + 1) rfl hS hT α x

/-- For a scheme X in universe u and c = max(u, w), every short exact
sequence S of AddCommGrpCat c-valued sheaves on the small étale site has
δ_S(x) = [S] ∘ x in every nonnegative degree. For every morphism α : S → T
between two such short exact sequences, these maps obey
δ_T ∘ Hⁿ(α₃) = Hⁿ⁺¹(α₁) ∘ δ_S. -/
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
