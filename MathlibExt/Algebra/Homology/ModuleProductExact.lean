/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Exact products of original module short complexes

The product maps act componentwise through the original differentials.
Exactness is proved by choosing the original component preimages. The
construction also applies to the finite shifted coefficient systems used
in generalized-cohomology descent, including an empty index.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R] {I : Type v} (S : I → ShortComplex (ModuleCat.{max u v} R))

/-- The product of the original module short complexes with their literal component maps. -/
def moduleProduct : ShortComplex (ModuleCat.{max u v} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.pi (fun i => (S i).f.hom.comp (LinearMap.proj i))))
    (ModuleCat.ofHom (LinearMap.pi (fun i => (S i).g.hom.comp (LinearMap.proj i))))
    (by
      apply ModuleCat.hom_ext
      ext x i
      exact ConcreteCategory.congr_hom (S i).zero (x i))

/-- Every product cycle has an original componentwise preimage when the component complexes are exact. -/
theorem moduleProduct_exact (hS : ∀ i, (S i).Exact) : (moduleProduct S).Exact := by
  rw [moduleCat_exact_iff]
  intro x hx
  have hxi (i : I) : (S i).g (x i) = 0 := congrFun hx i
  have hpre (i : I) : ∃ y : (S i).X₁, (S i).f y = x i :=
    (moduleCat_exact_iff (S i)).mp (hS i) (x i) (hxi i)
  choose y hy using hpre
  refine ⟨y, ?_⟩
  funext i
  exact hy i

section Finite

variable [Finite I]

/-- The standard biproduct/product comparison at an arbitrary finite index universe. -/
def moduleBiproductIsoPi (X : I → ModuleCat.{max u v} R) :
    (⨁ X) ≅ ModuleCat.of R (∀ i, X i) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit X) (ModuleCat.HasLimit.productLimitCone X).isLimit

theorem moduleBiproductIsoPi_inv_comp_π (X : I → ModuleCat.{max u v} R) (i : I) :
    (moduleBiproductIsoPi X).inv ≫ biproduct.π X i =
      ModuleCat.ofHom (LinearMap.proj i : (∀ j, X j) →ₗ[R] X i) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk i)

/-- The literal finite biproduct complex uses the original component maps. -/
def moduleBiproduct : ShortComplex (ModuleCat.{max u v} R) :=
  ShortComplex.mk (biproduct.map (fun i : I => (S i).f)) (biproduct.map (fun i : I => (S i).g)) (by
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, zero_comp]
    rw [← Category.assoc, biproduct.map_π, Category.assoc, (S i).zero, comp_zero])

theorem moduleBiproductIsoPi_map {X Y : I → ModuleCat.{max u v} R}
    (f : ∀ i, X i ⟶ Y i) :
    (moduleBiproductIsoPi X).hom ≫
      ModuleCat.ofHom (LinearMap.pi (fun i => (f i).hom.comp (LinearMap.proj i))) =
      biproduct.map f ≫ (moduleBiproductIsoPi Y).hom := by
  apply (cancel_epi (moduleBiproductIsoPi X).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  ext x i
  have hy : (moduleBiproductIsoPi Y).hom ≫
      ModuleCat.ofHom (LinearMap.proj i : (∀ j, Y j) →ₗ[R] Y i) = biproduct.π Y i := by
    apply (cancel_epi (moduleBiproductIsoPi Y).inv).mp
    simp only [Iso.inv_hom_id_assoc, moduleBiproductIsoPi_inv_comp_π]
  have hf := congrArg (fun g => (moduleBiproductIsoPi X).inv ≫ g) (biproduct.map_π f i)
  rw [← hy] at hf
  rw [← Category.assoc (moduleBiproductIsoPi X).inv (biproduct.π X i) (f i),
    moduleBiproductIsoPi_inv_comp_π] at hf
  exact (ConcreteCategory.congr_hom hf x).symm

/-- The standard finite biproduct/product equivalences preserve the original differentials. -/
def moduleBiproductIsoProduct : moduleBiproduct S ≅ moduleProduct S :=
  ShortComplex.isoMk (moduleBiproductIsoPi (fun i : I => (S i).X₁))
    (moduleBiproductIsoPi (fun i : I => (S i).X₂))
    (moduleBiproductIsoPi (fun i : I => (S i).X₃))
    (moduleBiproductIsoPi_map (fun i : I => (S i).f))
    (moduleBiproductIsoPi_map (fun i : I => (S i).g))

/-- Exactness of each component proves exactness of the literal finite shifted-source biproduct. -/
theorem moduleBiproduct_exact (hS : ∀ i, (S i).Exact) : (moduleBiproduct S).Exact :=
  ShortComplex.exact_of_iso (moduleBiproductIsoProduct S).symm (moduleProduct_exact S hS)

end Finite

end CategoryTheory.ShortComplex
