/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexRegularResolution
public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientTensor
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Exact coefficient sequences for finite Koszul complexes

Tensoring the free terms of a finite-family Koszul complex preserves a
short exact sequence of coefficient modules. The induced maps form a short
exact sequence of tensor complexes. The coefficient and term carriers may
lie in independent universes.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The actual coefficient tensor complex of the original finite family. -/
def familyTensorCoefficientComplex (a : Fin n → R) (M : ModuleCat.{v} R) :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ((coefficientTensorFunctor R M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (familyComplex R a)

/-- Original coefficient maps induce literal maps of the tensor complexes. -/
def familyTensorCoefficientMap (a : Fin n → R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    familyTensorCoefficientComplex R a M ⟶ familyTensorCoefficientComplex R a N :=
  (NatTrans.mapHomologicalComplex ((coefficientTensoringLeft R).map f)
    (ComplexShape.down ℕ)).app (familyComplex R a)

/-- The original coefficient short complex gives an actual tensor short complex. -/
def familyTensorCoefficientShortComplex (a : Fin n → R)
    (S : ShortComplex (ModuleCat.{v} R)) :
    ShortComplex (ChainComplex (ModuleCat.{max u v} R) ℕ) :=
  ShortComplex.mk (familyTensorCoefficientMap R a S.f)
    (familyTensorCoefficientMap R a S.g) (by
      apply HomologicalComplex.hom_ext
      intro j
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro m
      apply LinearMap.ext
      intro x
      change (S.g (S.f m)) ⊗ₜ[R] x = 0
      have hm : S.g (S.f m) = 0 :=
        congrArg (fun f : S.X₁ ⟶ S.X₃ => f m) S.zero
      rw [hm, TensorProduct.zero_tmul])

/-- The original equal-universe coefficient complex is unchanged as an
object, including every actual differential. -/
theorem familyTensorCoefficientComplex_sameUniverse
    (a : Fin n → R) (M : ModuleCat.{u} R) :
    familyTensorCoefficientComplex R a M =
      ((((tensoringLeft (ModuleCat.{u} R)).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (familyComplex R a)) := by
  simp only [familyTensorCoefficientComplex, coefficientTensorFunctor_sameUniverse]

/-- Every original equal-universe coefficient chain map is unchanged. -/
theorem familyTensorCoefficientMap_sameUniverse
    (a : Fin n → R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    familyTensorCoefficientMap R a f =
      (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map f)
        (ComplexShape.down ℕ)).app (familyComplex R a) := by
  apply HomologicalComplex.hom_ext
  intro j
  apply ModuleCat.hom_ext
  change TensorProduct.map f.hom LinearMap.id =
    f.hom.rTensor ((familyComplex R a).X j)
  rfl

/-- The Koszul tensor coefficient complex preserves every actual
short exact coefficient sequence, by freeness of its original terms. -/
theorem familyTensorCoefficientShortComplex_shortExact
    (a : Fin n → R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (familyTensorCoefficientShortComplex R a S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  let K := (familyComplex R a).X j
  let : Module.Free R K := familyComplex_free R a j
  let : Module.Flat R K := inferInstance
  let T := (familyTensorCoefficientShortComplex R a S).map
    (HomologicalComplex.eval _ _ j)
  exact ModuleCat.shortComplex_shortExact T
    (Module.Flat.rTensor_exact K
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact))
    (Module.Flat.rTensor_preserves_injective_linearMap S.f.hom hS.moduleCat_injective_f)
    (LinearMap.rTensor_surjective K hS.moduleCat_surjective_g)

end KoszulComplex
