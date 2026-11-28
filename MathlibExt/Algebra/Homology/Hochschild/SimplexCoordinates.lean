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
# Ordinal-surjection coordinates on Hochschild chains

Let k be a commutative ring, A a possibly noncommutative k-algebra, and M an A-bimodule with
compatible k-action. A simplex morphism f : [p] → [q] acts contravariantly from M ⊗ A⊗q to M ⊗
A⊗p. When f is surjective, it keeps the coefficient m and pulls back each edge label; a
constant edge receives the unit of A. This is the tensor formula for compositions of
simplicial degeneracies.

For the coefficient Hochschild simplicial module, see J.-L. Loday, Cyclic Homology, 2nd ed.,
Chapter 1.
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

/-- The contravariant simplex map on coefficient Hochschild tensors.

For a commutative ring k, an associative k-algebra A and a compatible A-bimodule M, f : X → Y
in Δ induces M ⊗ A⊗Y.len → M ⊗ A⊗X.len through the coefficient bar coordinates. -/
def simplexMap {X Y : SimplexCategory} (f : X ⟶ Y) :
    chainLevel k A M Y.len ⟶ chainLevel k A M X.len :=
  (coefficientBarObjIso k A M Y.len).inv ≫
    (coefficientBar k A M).map f.op ≫ (coefficientBarObjIso k A M X.len).hom

/-- The identity simplex acts identically on Hochschild tensors.

For a commutative ring k, an associative k-algebra A and a compatible A-bimodule M,
simplexMap(id_X) is the identity on M ⊗ A⊗X.len. -/
@[simp]
theorem simplexMap_id (X : SimplexCategory) :
    simplexMap k A M (𝟙 X) = 𝟙 _ := by
  rw [simplexMap, op_id, (coefficientBar k A M).map_id (Opposite.op X)]
  simp only [Category.id_comp, Iso.inv_hom_id]

/-- Composition reverses in the Hochschild simplex action.

For a commutative ring k, an associative k-algebra A, a compatible A-bimodule M and composable
simplex maps f,g, simplexMap(f ≫ g) = simplexMap(g) ≫ simplexMap(f). -/
@[reassoc]
theorem simplexMap_comp {X Y Z : SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    simplexMap k A M (f ≫ g) = simplexMap k A M g ≫ simplexMap k A M f := by
  simp only [simplexMap, op_comp, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- An elementary simplex surjection is a Hochschild degeneracy.

For a commutative ring k, an associative k-algebra A and a compatible A-bimodule M, the
simplex map σᵢ acts as degeneracy(n,i), inserting an algebra unit into the tensor word. -/
theorem simplexMap_σ (n : ℕ) (i : Fin (n + 1)) :
    simplexMap k A M (SimplexCategory.σ i) = degeneracy k A M n i := rfl

/-- The tensor-word action of an epimorphic simplex map.

For a commutative ring k, an associative k-algebra A, a compatible A-bimodule M and an
epimorphism f : X → Y, simplexMap(f)(m ⊗ tprod(a)) = m ⊗ tprod(pullbackEdges(f,a)). Constant
edges of f contribute 1_A. -/
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

/-- The tensor-word action of a surjective ordinal map.

For a commutative ring k, an associative k-algebra A, a compatible A-bimodule M and a simplex
map whose order map is surjective, the coefficient stays m and the edge word becomes
pullbackEdges(f,a). -/
theorem simplexMap_of_surjective_tprod {X Y : SimplexCategory} (f : X ⟶ Y)
    (hf : Function.Surjective f.toOrderHom) (m : M) (a : Fin Y.len → A) :
    (simplexMap k A M f).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (SimplexCategory.pullbackEdges f a) := by
  letI : Epi f := SimplexCategory.epi_iff_surjective.mpr hf
  exact simplexMap_of_epi_tprod k A M f m a

end ModuleCat.Algebra.Hochschild
