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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.BoundedSupport
public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Coordinates

/-!
# Finite coordinates in the Hom–tensor comparison

Coordinate projections apply at arbitrary displayed degrees, with independent
tensor-factor universes. Single-coordinate insertion is linear on its supported
degree.
-/

@[expose] public section
noncomputable section

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Native single-coordinate insertion, bundled on the original supported degree. -/
def cochainSingleLinear (P J : CochainComplex (ModuleCat.{v} R) ℤ)
    (a p j : ℤ) (hpj : p + a = j) :
    (P.X p →ₗ[R] J.X j) →ₗ[R] Cochain P J a where
  toFun f := Cochain.single (ModuleCat.ofHom f) a
  map_add' f g := by
    apply Cochain.ext
    intro p' j' hpj'
    by_cases hp : p' = p
    · subst p'
      have hj : j' = j := by omega
      subst hj
      simp only [Cochain.single_v, Cochain.add_v]
      rfl
    · rw [Cochain.add_v,
        Cochain.single_v_eq_zero (ModuleCat.ofHom (f + g)) a p' j' hpj' hp,
        Cochain.single_v_eq_zero (ModuleCat.ofHom f) a p' j' hpj' hp,
        Cochain.single_v_eq_zero (ModuleCat.ofHom g) a p' j' hpj' hp,
        zero_add]
  map_smul' r f := by
    apply Cochain.ext
    intro p' j' hpj'
    by_cases hp : p' = p
    · subst p'
      have hj : j' = j := by omega
      subst hj
      simp only [RingHom.id_apply, Cochain.single_v, Cochain.smul_v]
      rfl
    · rw [Cochain.smul_v,
        Cochain.single_v_eq_zero (ModuleCat.ofHom (r • f)) a p' j' hpj' hp,
        Cochain.single_v_eq_zero (ModuleCat.ofHom f) a p' j' hpj' hp,
        smul_zero]

/-- The insertion keeps the original actual coefficient map at the supported coordinate. -/
theorem cochainSingleLinear_v (P J : CochainComplex (ModuleCat.{v} R) ℤ)
    (a p j : ℤ) (hpj : p + a = j) (f : P.X p →ₗ[R] J.X j) :
    (cochainSingleLinear R P J a p j hpj f).v p j hpj = ModuleCat.ofHom f :=
  Cochain.single_v _ _ _

/-- Two supported presentations retain exactly the same original single cochain. -/
theorem cochain_single_coordinate_eq (P J : CochainComplex (ModuleCat.{v} R) ℤ)
    (a : ℤ) (f : Cochain P J a) (p j j' : ℤ)
    (hpj : p + a = j) (hpj' : p + a = j') :
    Cochain.single (f.v p j hpj) a = Cochain.single (f.v p j' hpj') a := by
  subst j
  subst j'
  rfl

end CochainComplex.ModuleTensor
