/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/Symmetric.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Tensor

/-!
# The symmetric monoidal category of modules over a commutative monoid

Let `A` be a commutative monoid object in a symmetric monoidal category `C` with coequalizers
preserved by tensoring. The balanced tensor product `M ⊗_A N` of `TauCeti`'s
`Mod.monoidalCategory` is then symmetric: the symmetry `M ⊗ N ≅ N ⊗ M` of `C` descends to an
isomorphism `M ⊗_A N ≅ N ⊗_A M` of `A`-modules, and these isomorphisms satisfy the hexagon
identities and square to the identity. This makes `Mod C A` a symmetric monoidal category, so
commutative monoids in it (Mathlib's `IsCommMonObj` and `CommMon`) make sense. For the
commutative sphere monoid in symmetric sequences this is the symmetric monoidal structure on the
smash product of symmetric spectra, whose commutative monoids are the commutative symmetric ring
spectra.

The symmetry of `C` is used already for the braiding to be well defined on the quotient
`M ⊗_A N`, not only for its symmetry: the balancing relation moves scalars between the factors
through the inverse braiding, and in a merely braided category the braiding of the factors need
not respect it.

## Main definitions

* `Mod.symmetricCategory`: modules over a commutative monoid object in a symmetric monoidal
  category form a symmetric monoidal category under the balanced tensor product.

## Main statements

* `Mod.braiding_tensorπ_condition` and `Mod.smul_tensorDesc_braiding`: the braiding of the
  underlying objects descends to an `A`-linear map `M ⊗_A N ⟶ N ⊗_A M`.
* `Mod.tensorπ_braiding_hom_hom` and `Mod.tensorπ_braiding_inv_hom`: the braiding of `Mod C A` on
  representatives in `M.X ⊗ N.X`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonObj BraidedCategory Limits

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A]

/-- The braiding of the underlying objects, followed by the quotient map onto `N ⊗_A M`, identifies
the actions of `A` on `M` and on `N`. -/
theorem braiding_tensorπ_condition (M N : Mod C A) :
    ((β_ A M.X).inv ≫ γ[A, M.X]) ▷ N.X ≫ (β_ M.X N.X).hom ≫ tensorπ N M =
      (α_ M.X A N.X).hom ≫ M.X ◁ γ[A, N.X] ≫ (β_ M.X N.X).hom ≫ tensorπ N M := by
  -- Both sides move the scalar past the other factor; in `N ⊗_A M` the scalar may act on either
  -- factor, and the two resulting permutations of `M ⊗ A ⊗ N` agree by the Yang–Baxter equation
  -- once the inverse braiding is rewritten as a braiding using the symmetry.
  have hcoh : (β_ (M.X ⊗ A) N.X).hom ≫ N.X ◁ (β_ A M.X).inv =
      (α_ M.X A N.X).hom ≫ (β_ M.X (A ⊗ N.X)).hom ≫ (β_ A N.X).hom ▷ M.X ≫
        (α_ N.X A M.X).hom := by
    rw [← SymmetricCategory.braiding_swap_eq_inv_braiding, braiding_tensor_left_hom,
      braiding_tensor_right_hom]
    simp only [Category.assoc]
    rw [yang_baxter]
  rw [comp_whiskerRight, Category.assoc, braiding_naturality_left_assoc,
    braiding_naturality_left_assoc, braiding_naturality_right_assoc, smul_whiskerRight_tensorπ,
    reassoc_of% hcoh]

/-- The morphism `M ⊗_A N ⟶ N ⊗_A M` induced by the braiding `M ⊗ N ⟶ N ⊗ M` of the underlying
objects is `A`-linear: the scalars act on `M ⊗_A N` through `M` and on `N ⊗_A M` through `N`, and
these agree on `N ⊗_A M` by the balancing relation. -/
theorem smul_tensorDesc_braiding (M N : Mod C A) :
    γ[A, (M ⊗ N).X] ≫
        tensorDesc ((β_ M.X N.X).hom ≫ tensorπ N M) (braiding_tensorπ_condition M N) =
      A ◁ tensorDesc ((β_ M.X N.X).hom ≫ tensorπ N M) (braiding_tensorπ_condition M N) ≫
        γ[A, (N ⊗ M).X] := by
  rw [← cancel_epi (A ◁ tensorπ M N), whiskerLeft_tensorπ_smul_assoc, tensorπ_tensorDesc,
    whiskerLeft_tensorπ_tensorDesc_assoc, whiskerLeft_comp_assoc, whiskerLeft_tensorπ_smul,
    smul_whiskerRight_tensorπ, braiding_naturality_left_assoc]
  -- The action `γ` of `A` on `M.X` has source the action object of `A` on `M.X`, which is only
  -- definitionally `A ⊗ M.X`, so `rw` cannot expand the braiding of that source by the hexagon
  -- identity; `simp` can.
  simp

/-- Modules over a commutative monoid object in a symmetric monoidal category form a symmetric
monoidal category under the balanced tensor product, with braiding induced by that of `C`. -/
noncomputable instance symmetricCategory : SymmetricCategory (Mod C A) where
  braiding M N :=
    { hom := Hom.mk' (tensorDesc _ (braiding_tensorπ_condition M N)) (smul_tensorDesc_braiding M N)
      inv := Hom.mk' (tensorDesc _ (braiding_tensorπ_condition N M)) (smul_tensorDesc_braiding N M)
      hom_inv_id := by
        ext
        simp
      inv_hom_id := by
        ext
        simp }
  braiding_naturality_right M N N' g := by
    ext
    simp
  braiding_naturality_left f N := by
    ext
    simp
  hexagon_forward M N P := by
    apply hom_ext
    rw [← cancel_epi (tensorπ M N ▷ P.X ≫ tensorπ (M ⊗ N) P)]
    simp [tensorπ_associator_hom_hom, tensorπ_associator_hom_hom_assoc]
  hexagon_reverse M N P := by
    apply hom_ext
    rw [← cancel_epi (M.X ◁ tensorπ N P ≫ tensorπ M (N ⊗ P))]
    simp [tensorπ_associator_inv_hom, tensorπ_associator_inv_hom_assoc]
  symmetry M N := by
    ext
    simp

/-- On representatives, the braiding `M ⊗_A N ≅ N ⊗_A M` is the braiding of the underlying
objects. -/
@[reassoc (attr := simp)]
theorem tensorπ_braiding_hom_hom (M N : Mod C A) :
    tensorπ M N ≫ (β_ M N).hom.hom = (β_ M.X N.X).hom ≫ tensorπ N M :=
  -- The braiding of `Mod C A` is defined as this factorization through the quotient map.
  tensorπ_tensorDesc _ _

/-- On representatives, the inverse braiding `N ⊗_A M ≅ M ⊗_A N` is the inverse braiding of the
underlying objects. -/
@[reassoc (attr := simp)]
theorem tensorπ_braiding_inv_hom (M N : Mod C A) :
    tensorπ N M ≫ (β_ M N).inv.hom = (β_ M.X N.X).inv ≫ tensorπ M N := by
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding M N,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding M.X N.X]
  exact tensorπ_tensorDesc _ _

end Mod

end CategoryTheory
