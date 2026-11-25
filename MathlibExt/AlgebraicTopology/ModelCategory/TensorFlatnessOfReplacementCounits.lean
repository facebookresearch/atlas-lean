/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# Tensor flatness from replacement counits

In a closed symmetric monoidal model category, let `Q` have cofibrant values and a
natural weak-equivalence counit to the identity. For a cofibrant object `K`, if left
tensoring by `K` preserves these counits, it preserves every weak equivalence.
The proof combines Brown preservation on the cofibrant values of `Q` with counit
naturality and two-out-of-three; the braiding transfers the result to right tensoring.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open CategoryTheory.BraidedCategory

namespace HomotopicalAlgebra.TensorFlatnessOfReplacementCounits

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C] in
/-- The natural replacement square, and both original counits, give the weak Q map. -/
theorem replacement_map_weak (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
    (hε : ∀ X : C, weakEquivalences C (ε.app X))
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C (Q.map f) := by
  have h := ε.naturality f
  change Q.map f ≫ ε.app Y = ε.app X ≫ f at h
  apply (weakEquivalences C).of_postcomp _ _ (hε Y)
  rw [h]
  exact (weakEquivalences C).comp_mem _ _ (hε X) hf

/-- A cofibrant left tensor preserves every weak original arrow after both actual Q-counit
comparisons. -/
theorem leftTensor_weak_of_replacementCounits
    (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
    (hQ : ∀ X : C, IsCofibrant (Q.obj X))
    (hε : ∀ X : C, weakEquivalences C (ε.app X))
    (K : C) [IsCofibrant K]
    (hKε : ∀ X : C, weakEquivalences C (K ◁ ε.app X))
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C (K ◁ f) := by
  let : IsCofibrant (Q.obj X) := hQ X
  let : IsCofibrant (Q.obj Y) := hQ Y
  let : WeakEquivalence (Q.map f) := (weakEquivalence_iff _).mpr (replacement_map_weak Q ε hε f hf)
  let : (ihom.adjunction K).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  have hKQ : weakEquivalences C (K ◁ Q.map f) :=
    (weakEquivalence_iff _).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := ihom.adjunction K)
        (Q.map f))
  have hNat := congrArg (fun g => K ◁ g) (ε.naturality f)
  change (K ◁ (Q.map f ≫ ε.app Y)) = (K ◁ (ε.app X ≫ f)) at hNat
  simp only [whiskerLeft_comp] at hNat
  apply (weakEquivalences C).of_precomp _ _ (hKε X)
  rw [← hNat]
  exact (weakEquivalences C).comp_mem _ _ hKQ (hKε Y)

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The actual braiding transports left tensor flatness to the needed right coefficient order. -/
theorem rightTensor_weak_of_leftTensor {X Y : C} (f : X ⟶ Y) (K : C)
    (h : weakEquivalences C (K ◁ f)) : weakEquivalences C (f ▷ K) := by
  let e : Arrow.mk (f ▷ K) ≅ Arrow.mk (K ◁ f) :=
    Arrow.isoMk (β_ X K) (β_ Y K) (braiding_naturality_left f K).symm
  exact ((weakEquivalences C).arrow_mk_iso_iff e).mpr h

end HomotopicalAlgebra.TensorFlatnessOfReplacementCounits
