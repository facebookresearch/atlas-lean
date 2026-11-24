/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairing
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Actual truncated chain pairings and their quotient complexes

The canonical truncation inclusions restrict an existing chain pairing.
Its native cokernel is therefore an actual quotient complex. Morphisms
of the original pairings induce canonical quotient maps, with their
original projection squares, identities and composition laws.

For nonnegative chains the embedding by addition of one selects the
positive part. Its lowest retained object is the original cycle object.
When the degree-one boundary vanishes, that cycle object is canonically
the whole original degree-one object. Identification of the resulting
image with the sum of all positive pairing components is a separate law.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe v u

namespace HomologicalComplex.ChainGradedPairing

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [CategoryTheory.MonoidalPreadditive C]
  (e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ)) [e.IsTruncLE]

section Objects

variable {K₁ K₂ K₃ : ChainComplex C ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)

/-- Restrict the actual pairing along the two original canonical truncation inclusions. -/
def truncationPairing : ChainGradedPairing (K₁.truncLE e) (K₂.truncLE e) K₃ :=
  tensorHom (K₁.ιTruncLE e) (K₂.ιTruncLE e) ≫ P

/-- Every truncated component is the original component after the actual inclusions. -/
@[reassoc]
theorem truncationPairing_pair (p q : ℕ) :
    pair (truncationPairing e P) p q =
      ((K₁.ιTruncLE e).f p ⊗ₘ (K₂.ιTruncLE e).f q) ≫ pair P p q := by
  have h := pair_naturality (truncationPairing e P) P
    (K₁.ιTruncLE e) (K₂.ιTruncLE e) (𝟙 K₃)
    (by simp only [truncationPairing, Category.comp_id]) p q
  simpa using h.symm

/-- The native cokernel of the actual truncated pairing is a quotient complex. -/
def truncationQuotient : ChainComplex C ℕ := cokernel (truncationPairing e P)

/-- The original target complex maps through its actual cokernel projection. -/
def truncationProjection : K₃ ⟶ truncationQuotient e P :=
  cokernel.π (truncationPairing e P)

/-- The quotient kills the original truncated pairing by its cokernel universal property. -/
@[reassoc]
theorem truncationPairing_comp_projection :
    truncationPairing e P ≫ truncationProjection e P = 0 :=
  cokernel.condition _

end Objects

section Maps

variable {K₁ K₂ K₃ L₁ L₂ L₃ : ChainComplex C ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃) (Q : ChainGradedPairing L₁ L₂ L₃)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)


/-- Original pairing compatibility implies compatibility of the actual truncation maps. -/
@[reassoc]
theorem truncationPairing_naturality (h : tensorHom f₁ f₂ ≫ Q = P ≫ f₃) :
    tensorHom (truncLEMap f₁ e) (truncLEMap f₂ e) ≫ truncationPairing e Q =
      truncationPairing e P ≫ f₃ := by
  calc
    _ = tensorHom (K₁.ιTruncLE e) (K₂.ιTruncLE e) ≫ (tensorHom f₁ f₂ ≫ Q) := by
      rw [truncationPairing, ← Category.assoc, tensorHom_comp_tensorHom,
        ιTruncLE_naturality, ιTruncLE_naturality,
        ← tensorHom_comp_tensorHom, Category.assoc]
    _ = tensorHom (K₁.ιTruncLE e) (K₂.ιTruncLE e) ≫ (P ≫ f₃) := by rw [h]
    _ = _ := by simp only [truncationPairing, Category.assoc]

/-- A morphism of the actual pairings induces the native quotient map. -/
def truncationQuotientMap (h : tensorHom f₁ f₂ ≫ Q = P ≫ f₃) : truncationQuotient e P ⟶ truncationQuotient e Q :=
  cokernel.map (truncationPairing e P) (truncationPairing e Q)
    (tensorHom (truncLEMap f₁ e) (truncLEMap f₂ e)) f₃
    (truncationPairing_naturality e P Q f₁ f₂ f₃ h).symm

/-- The native induced quotient map retains the original target chain-map square. -/
@[reassoc]
theorem truncationProjection_map (h : tensorHom f₁ f₂ ≫ Q = P ≫ f₃) :
    truncationProjection e P ≫ truncationQuotientMap e P Q f₁ f₂ f₃ h =
      f₃ ≫ truncationProjection e Q :=
  cokernel.π_desc _ _ _

end Maps

section Functoriality

variable {K₁ K₂ K₃ : ChainComplex C ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)

/-- The actual identity morphism of pairings induces the identity quotient map. -/
@[simp]
theorem truncationQuotientMap_id :
    truncationQuotientMap e P P (𝟙 K₁) (𝟙 K₂) (𝟙 K₃)
      (by simp only [tensorHom_id_id, Category.id_comp, Category.comp_id]) =
        𝟙 (truncationQuotient e P) := by
  apply (cancel_epi (cokernel.π (truncationPairing e P))).1
  change truncationProjection e P ≫ _ = truncationProjection e P ≫ _
  rw [truncationProjection_map, Category.id_comp, Category.comp_id]

end Functoriality

/-- Composition of pairing morphisms gives composition of native quotient maps. -/
@[reassoc]
theorem truncationQuotientMap_comp
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ)) [e.IsTruncLE]
    {K₁ K₂ K₃ L₁ L₂ L₃ M₁ M₂ M₃ : ChainComplex C ℕ}
    (P : ChainGradedPairing K₁ K₂ K₃) (Q : ChainGradedPairing L₁ L₂ L₃)
    (S : ChainGradedPairing M₁ M₂ M₃)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (g₁ : L₁ ⟶ M₁) (g₂ : L₂ ⟶ M₂) (g₃ : L₃ ⟶ M₃)
    (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)
    (hg : tensorHom g₁ g₂ ≫ S = Q ≫ g₃) :
    truncationQuotientMap e P Q f₁ f₂ f₃ hf ≫
        truncationQuotientMap e Q S g₁ g₂ g₃ hg =
      truncationQuotientMap e P S (f₁ ≫ g₁) (f₂ ≫ g₂) (f₃ ≫ g₃)
        (by rw [← tensorHom_comp_tensorHom, Category.assoc, hg,
          ← Category.assoc, hf, Category.assoc]) := by
  apply (cancel_epi (cokernel.π (truncationPairing e P))).1
  change truncationProjection e P ≫ _ = truncationProjection e P ≫ _
  rw [← Category.assoc, truncationProjection_map, Category.assoc,
    truncationProjection_map, truncationProjection_map, Category.assoc]

end HomologicalComplex.ChainGradedPairing
