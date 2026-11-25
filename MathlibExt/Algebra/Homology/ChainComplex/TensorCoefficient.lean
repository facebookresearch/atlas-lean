/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor coefficients on a chain complex of modules

Tensoring a short exact sequence of coefficients with a chain complex whose
terms are flat gives a degreewise short exact sequence. The coefficient module
occurs first in each tensor product. The ring, coefficient and chain-term
universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v t

namespace ChainComplex.TensorCoefficient

variable (R : Type u) [CommRing R] (K : ChainComplex (ModuleCat.{v} R) ℕ)

/-- The actual coefficient complex, keeping the original first tensor factor. -/
def functor : ModuleCat.{t} R ⥤ ChainComplex (ModuleCat.{max v t} R) ℕ where
  obj M := (((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  map f := (NatTrans.mapHomologicalComplex
    ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map f)
    (ComplexShape.down ℕ)).app K
  map_id M := by
    rw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

instance functor_additive : (functor.{u, v, t} R K).Additive where
  map_add {M N f g} := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m x
    change TensorProduct.map (f.hom + g.hom) LinearMap.id (m ⊗ₜ[R] x) =
      TensorProduct.map f.hom LinearMap.id (m ⊗ₜ[R] x) +
        TensorProduct.map g.hom LinearMap.id (m ⊗ₜ[R] x)
    simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply,
      TensorProduct.add_tmul]

/-- Coefficient maps act on the actual first factor in every chain degree. -/
theorem map_tmul {M N : ModuleCat.{t} R} (f : M ⟶ N) (n : ℕ)
    (m : M) (x : K.X n) :
    (((functor R K).map f).f n).hom (m ⊗ₜ[R] x) = f.hom m ⊗ₜ[R] x := by
  change TensorProduct.map f.hom LinearMap.id (m ⊗ₜ[R] x) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]

/-- The actual differential keeps the original coefficient unchanged. -/
theorem differential_tmul (M : ModuleCat.{t} R) (i j : ℕ)
    (m : M) (x : K.X i) :
    (((functor R K).obj M).d i j).hom (m ⊗ₜ[R] x) =
      m ⊗ₜ[R] (K.d i j).hom x := by
  change TensorProduct.map LinearMap.id (K.d i j).hom (m ⊗ₜ[R] x) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]

variable {K} {L : ChainComplex (ModuleCat.{v} R) ℕ}

/-- A genuine chain map induces a natural transformation in arbitrary coefficients. -/
def map (f : K ⟶ L) : functor.{u, v, t} R K ⟶ functor R L where
  app M := (((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).map f
  naturality {M N} g := by
    exact ((NatTrans.mapHomologicalComplex
      ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map g)
      (ComplexShape.down ℕ)).naturality f).symm

theorem map_chain_tmul (f : K ⟶ L) (M : ModuleCat.{t} R) (n : ℕ)
    (m : M) (x : K.X n) :
    (((map R f).app M).f n).hom (m ⊗ₜ[R] x) =
      m ⊗ₜ[R] (f.f n).hom x := by
  change TensorProduct.map LinearMap.id (f.f n).hom (m ⊗ₜ[R] x) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]

theorem map_id (K : ChainComplex (ModuleCat.{v} R) ℕ) :
    map.{u, v, t} R (𝟙 K) = 𝟙 (functor R K) := by
  apply NatTrans.ext
  funext M
  exact CategoryTheory.Functor.map_id
    (((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M).mapHomologicalComplex (ComplexShape.down ℕ)) K

theorem map_comp {T : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ T) :
    map.{u, v, t} R (f ≫ g) = map R f ≫ map R g := by
  apply NatTrans.ext
  funext M
  exact CategoryTheory.Functor.map_comp
    (((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M).mapHomologicalComplex (ComplexShape.down ℕ)) f g

/-- A genuine chain isomorphism induces the natural isomorphism on the same coefficients. -/
def mapIso (e : K ≅ L) : functor.{u, v, t} R K ≅ functor R L where
  hom := map R e.hom
  inv := map R e.inv
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

variable (K)

/-- Flatness of the actual second-factor terms earns degreewise coefficient exactness. -/
theorem shortExact (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) :
    (S.map (functor R K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  letI : Module.Flat R (K.X n) := hK n
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (S.f.hom.rTensor (K.X n)) (S.g.hom.rTensor (K.X n))
    exact Module.Flat.rTensor_exact (K.X n)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  · change Function.Injective (S.f.hom.rTensor (K.X n))
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := K.X n)
      S.f.hom hS.moduleCat_injective_f
  · change Function.Surjective (S.g.hom.rTensor (K.X n))
    exact LinearMap.rTensor_surjective (K.X n) hS.moduleCat_surjective_g

end ChainComplex.TensorCoefficient

end
