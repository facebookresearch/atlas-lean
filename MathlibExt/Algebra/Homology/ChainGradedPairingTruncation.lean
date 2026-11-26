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
# Chain pairings restricted to canonical truncations

Let C be an abelian monoidal category with tensor product additive in both variables. For a
shape embedding e : down ℕ → down ℕ which reflects arrows and whose image is closed under
incoming arrows, each chain complex has its canonical truncation K.truncLE e with inclusion
into K. It is zero outside the image, agrees with K away from the outgoing boundary, and uses
the cycle object at that boundary.

Composing a chain pairing with the tensor of the two truncation inclusions gives a pairing
into the same target complex. Its cokernel defines a quotient chain complex. Compatible maps
of pairings induce maps of these quotients which commute with the projections and preserve
identities and composition. All component degrees remain the ambient natural-number indices.
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

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. Define truncationPairing e P :
T₁ ⊗ T₂ ⟶ K₃ as tensorHom ι₁ ι₂ ≫ P. The canonical truncations retain the ambient ℕ indices
and use cycles at an outgoing boundary. -/
def truncationPairing : ChainGradedPairing (K₁.truncLE e) (K₂.truncLE e) K₃ :=
  tensorHom (K₁.ιTruncLE e) (K₂.ιTruncLE e) ≫ P

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. For p, q : ℕ, pair
(truncationPairing e P) p q = (ι₁.f p ⊗ₘ ι₂.f q) ≫ pair P p q as a morphism T₁.X p ⊗ T₂.X q ⟶
K₃.X (p + q). -/
@[reassoc]
theorem truncationPairing_pair (p q : ℕ) :
    pair (truncationPairing e P) p q =
      ((K₁.ιTruncLE e).f p ⊗ₘ (K₂.ιTruncLE e).f q) ≫ pair P p q := by
  have h := pair_naturality (truncationPairing e P) P
    (K₁.ιTruncLE e) (K₂.ιTruncLE e) (𝟙 K₃)
    (by simp only [truncationPairing, Category.comp_id]) p q
  simpa using h.symm

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. Define truncationQuotient e P
to be the cokernel in ChainComplex C ℕ of tensorHom ι₁ ι₂ ≫ P : T₁ ⊗ T₂ ⟶ K₃. -/
def truncationQuotient : ChainComplex C ℕ := cokernel (truncationPairing e P)

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. The map truncationProjection e
P : K₃ ⟶ truncationQuotient e P is the cokernel projection of truncationPairing e P. -/
def truncationProjection : K₃ ⟶ truncationQuotient e P :=
  cokernel.π (truncationPairing e P)

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. The chain maps satisfy
truncationPairing e P ≫ truncationProjection e P = 0, by the cokernel equation. -/
@[reassoc]
theorem truncationPairing_comp_projection :
    truncationPairing e P ≫ truncationProjection e P = 0 :=
  cokernel.condition _

end Objects

section Maps

variable {K₁ K₂ K₃ L₁ L₂ L₃ : ChainComplex C ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃) (Q : ChainGradedPairing L₁ L₂ L₃)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)


/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). Let P : K₁ ⊗ K₂ ⟶ K₃ and Q : L₁ ⊗ L₂ ⟶ L₃ be chain
pairings, and let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃. Then tensorHom
(truncLEMap f₁ e) (truncLEMap f₂ e) ≫ truncationPairing e Q = truncationPairing e P ≫ f₃. This
is a map from the tensor of the two truncated K-complexes to L₃. -/
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

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). Let P : K₁ ⊗ K₂ ⟶ K₃ and Q : L₁ ⊗ L₂ ⟶ L₃ be chain
pairings, and let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃. The resulting
commutative square induces truncationQuotientMap : truncationQuotient e P ⟶ truncationQuotient
e Q by the cokernel map, using the tensor of the truncated f₁ and f₂ on the source and f₃ on
the target. -/
def truncationQuotientMap (h : tensorHom f₁ f₂ ≫ Q = P ≫ f₃) : truncationQuotient e P ⟶ truncationQuotient e Q :=
  cokernel.map (truncationPairing e P) (truncationPairing e Q)
    (tensorHom (truncLEMap f₁ e) (truncLEMap f₂ e)) f₃
    (truncationPairing_naturality e P Q f₁ f₂ f₃ h).symm

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). Let P : K₁ ⊗ K₂ ⟶ K₃ and Q : L₁ ⊗ L₂ ⟶ L₃ be chain
pairings, and let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃. Let q(f) be the
induced map of truncated-pairing cokernels and π_P, π_Q their projections from K₃ and L₃. Then
π_P ≫ q(f) = f₃ ≫ π_Q. -/
@[reassoc]
theorem truncationProjection_map (h : tensorHom f₁ f₂ ≫ Q = P ≫ f₃) :
    truncationProjection e P ≫ truncationQuotientMap e P Q f₁ f₂ f₃ h =
      f₃ ≫ truncationProjection e Q :=
  cokernel.π_desc _ _ _

end Maps

section Functoriality

variable {K₁ K₂ K₃ : ChainComplex C ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. The map truncationQuotientMap
e P P (𝟙 K₁) (𝟙 K₂) (𝟙 K₃), with the identity compatibility equation, equals 𝟙
(truncationQuotient e P). -/
@[simp]
theorem truncationQuotientMap_id :
    truncationQuotientMap e P P (𝟙 K₁) (𝟙 K₂) (𝟙 K₃)
      (by simp only [tensorHom_id_id, Category.id_comp, Category.comp_id]) =
        𝟙 (truncationQuotient e P) := by
  apply (cancel_epi (cokernel.π (truncationPairing e P))).1
  change truncationProjection e P ≫ _ = truncationProjection e P ≫ _
  rw [truncationProjection_map, Category.id_comp, Category.comp_id]

end Functoriality

/-- Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). Let P, Q and S be pairings of triples K_i, L_i and M_i.
Let f_i : K_i ⟶ L_i and g_i : L_i ⟶ M_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃ and tensorHom g₁
g₂ ≫ S = Q ≫ g₃. Then the induced quotient map for f followed by that for g equals the
quotient map induced by the componentwise composites f_i ≫ g_i and their composed
compatibility equation. -/
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
