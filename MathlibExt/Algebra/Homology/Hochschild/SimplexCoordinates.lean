/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Simplicial
public import MathlibExt.AlgebraicTopology.SimplexCategory.EdgePullback
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-!
# Hochschild tensor coordinates of ordinal surjections

Every ordinal surjection acts on a Hochschild tensor word by
preserving the coefficient and inserting units along constant
edges. The formula uses the simplicial degeneracies and simplex
epi induction. The algebra may be noncommutative, and ground,
algebra and coefficient universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild

attribute [local instance] uliftSMulCommClass

variable (k : Type u) (A : Type v) (M : Type w)
  [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M]
  [Module A M] [Module Aᵐᵒᵖ M] [Module k M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M]
  [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Actual contravariant coefficient-bar action in its original tensor carrier. -/
def simplexMap {X Y : SimplexCategory} (f : X ⟶ Y) :
    chainLevel k A M Y.len ⟶ chainLevel k A M X.len :=
  (coefficientBarObjIso k A M Y.len).inv ≫
    (coefficientBar k A M).map f.op ≫ (coefficientBarObjIso k A M X.len).hom

/-- Identity maps act by the original identity tensor map. -/
@[simp]
theorem simplexMap_id (X : SimplexCategory) :
    simplexMap k A M (𝟙 X) = 𝟙 _ := by
  rw [simplexMap, op_id, (coefficientBar k A M).map_id (Opposite.op X)]
  simp only [Category.id_comp, Iso.inv_hom_id]

/-- The tensor-coordinate maps compose in contravariant order. -/
@[reassoc]
theorem simplexMap_comp {X Y Z : SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    simplexMap k A M (f ≫ g) = simplexMap k A M g ≫ simplexMap k A M f := by
  simp only [simplexMap, op_comp, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- The coordinate degeneracy is this same simplex map. -/
theorem simplexMap_σ (n : ℕ) (i : Fin (n + 1)) :
    simplexMap k A M (SimplexCategory.σ i) = degeneracy k A M n i := rfl

/-- Every epi inserts units on constant edges and selects labels on increasing edges. -/
theorem simplexMap_of_epi_tprod {X Y : SimplexCategory} (f : X ⟶ Y) [Epi f]
    (m : M) (a : Fin Y.len → A) :
    (simplexMap k A M f).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (SimplexCategory.pullbackEdges f a) := by
  let P : MorphismProperty SimplexCategory := fun {X Y} f =>
    ∀ (m : M) (a : Fin Y.len → A),
      (simplexMap k A M f).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        m ⊗ₜ[k] PiTensorProduct.tprod k (SimplexCategory.pullbackEdges f a)
  have hP : P f := SimplexCategory.epi_induction (motive := P)
    (fun X m a => by
      simp only [simplexMap_id, ModuleCat.hom_id,
        LinearMap.id_coe, id_eq, SimplexCategory.pullbackEdges_id])
    (fun {X Y} g i hg m a => by
      rw [simplexMap_comp, simplexMap_σ]
      change (degeneracy k A M X.len i).hom
        ((simplexMap k A M g).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
      rw [hg m a, degeneracy_tprod]
      rw [SimplexCategory.pullbackEdges_σ_comp]
      rfl) f
  exact hP m a

/-- Explicit surjectivity earns the epi premise of the original-coordinate dictionary. -/
theorem simplexMap_of_surjective_tprod {X Y : SimplexCategory} (f : X ⟶ Y)
    (hf : Function.Surjective f.toOrderHom) (m : M) (a : Fin Y.len → A) :
    (simplexMap k A M f).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (SimplexCategory.pullbackEdges f a) := by
  letI : Epi f := SimplexCategory.epi_iff_surjective.mpr hf
  exact simplexMap_of_epi_tprod k A M f m a

end ModuleCat.Algebra.Hochschild
