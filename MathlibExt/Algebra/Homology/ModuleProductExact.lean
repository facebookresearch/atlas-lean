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
# Exact products and finite biproducts of module short complexes

Let R be a ring in u and I an index type in v, with coefficient carriers W=max(u,v). The product
short complex has terms ∏_i A_i, ∏_i B_i, ∏_i C_i and maps acting coordinatewise. If every
component is exact at B_i, the product is exact at ∏_i B_i.

For finite I, the canonical finite biproduct-to-product isomorphisms commute with the component
maps. They give an isomorphism of the biproduct short complex with the product short complex, so
exactness also passes to the finite biproduct. The empty family is included.
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

/-- Let R be a ring in u, I a type in v, W=max(u,v), and S_i=(A_i --f_i→ B_i --g_i→ C_i) short
complexes of R-modules in W. The product has terms ∏_i A_i→∏_i B_i→∏_i C_i, with f(x)_i=f_i(x_i)
and g(y)_i=g_i(y_i). Since f_i≫g_i=0 in every component, the product composite is zero. -/
def moduleProduct : ShortComplex (ModuleCat.{max u v} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.pi (fun i => (S i).f.hom.comp (LinearMap.proj i))))
    (ModuleCat.ofHom (LinearMap.pi (fun i => (S i).g.hom.comp (LinearMap.proj i))))
    (by
      apply ModuleCat.hom_ext
      ext x i
      exact ConcreteCategory.congr_hom (S i).zero (x i))

/-- Let R be a ring in u, I a type in v, W=max(u,v), and S_i=(A_i --f_i→ B_i --g_i→ C_i) short
complexes of R-modules in W. If im(f_i)=ker(g_i) for every i, then the product short complex is
exact at ∏_i B_i. Every tuple y with g_i(y_i)=0 has a tuple preimage x with f_i(x_i)=y_i. -/
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

/-- Let R be a ring in u, I finite in v, W=max(u,v), and X_i∈ModuleCat_W(R). There is an isomorphism
e:⊕_i X_i≅∏_i X_i of R-module objects. The coordinate of e(x) at i is the i-th biproduct
projection of x, and the inverse sums the finitely many injections. -/
def moduleBiproductIsoPi (X : I → ModuleCat.{max u v} R) :
    (⨁ X) ≅ ModuleCat.of R (∀ i, X i) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit X)
    (ModuleCat.HasLimit.productLimitCone X).isLimit

theorem moduleBiproductIsoPi_inv_comp_π (X : I → ModuleCat.{max u v} R) (i : I) :
    (moduleBiproductIsoPi X).inv ≫ biproduct.π X i =
      ModuleCat.ofHom (LinearMap.proj i : (∀ j, X j) →ₗ[R] X i) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk i)

/-- Let R be a ring in u, I a type in v, W=max(u,v), and S_i=(A_i --f_i→ B_i --g_i→ C_i) short
complexes of R-modules in W. Assume I is finite. The short complex has terms ⊕_i A_i→⊕_i B_i→⊕_i
C_i and maps ⊕_i f_i, ⊕_i g_i. The component zero-composite equations give its zero composite. -/
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

/-- Let R be a ring in u, I a type in v, W=max(u,v), and S_i=(A_i --f_i→ B_i --g_i→ C_i) short
complexes of R-modules in W. For finite I, the three canonical isomorphisms ⊕_i A_i≅∏_i A_i, and
similarly for B_i,C_i, give an isomorphism from the biproduct short complex to the product short
complex. They intertwine both f and g. -/
def moduleBiproductIsoProduct : moduleBiproduct S ≅ moduleProduct S :=
  ShortComplex.isoMk (moduleBiproductIsoPi (fun i : I => (S i).X₁))
    (moduleBiproductIsoPi (fun i : I => (S i).X₂))
    (moduleBiproductIsoPi (fun i : I => (S i).X₃))
    (moduleBiproductIsoPi_map (fun i : I => (S i).f))
    (moduleBiproductIsoPi_map (fun i : I => (S i).g))

/-- Let R be a ring in u, I a type in v, W=max(u,v), and S_i=(A_i --f_i→ B_i --g_i→ C_i) short
complexes of R-modules in W. For finite I, if every S_i is exact, then the biproduct short
complex is exact at ⊕_i B_i. The biproduct/product comparison transports exactness from the
coordinatewise product. -/
theorem moduleBiproduct_exact (hS : ∀ i, (S i).Exact) : (moduleBiproduct S).Exact :=
  ShortComplex.exact_of_iso (moduleBiproductIsoProduct S).symm (moduleProduct_exact S hS)

end Finite

end CategoryTheory.ShortComplex
