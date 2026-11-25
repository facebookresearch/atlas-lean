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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.HomTensorDifferential

/-!
# Actual support bounds for the finite Hom–tensor comparison

These are the original zero-object bounds from the source contract. They
earn lower support of the actual Hom and tensor models, and the finite
P interval visible in each original Hom(P,J⊗U) degree.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Original upper/lower coefficient bounds give the actual lower Hom-complex bound. -/
theorem linearComplex_isZero_X_of_bounds
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (N L a : ℤ)
    (hP : ∀ p : ℤ, N < p → IsZero (P.X p))
    (hJ : ∀ j : ℤ, j < L → IsZero (J.X j)) (ha : a < L - N) :
    IsZero ((linearComplex R P J).X a) := by
  letI : Subsingleton ((linearComplex R P J).X a) := ⟨fun f g => by
    apply Cochain.ext
    intro p q hpq
    by_cases hp : N < p
    · exact (hP p hp).eq_of_src _ _
    · have hq : q < L := by omega
      exact (hJ q hq).eq_of_tgt _ _⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The original two lower bounds give the actual sum-tensor lower bound. -/
theorem complexAt_isZero_X_of_lower_bounds
    (J U : CochainComplex (ModuleCat.{v} R) ℤ) (L M n : ℤ)
    (hJ : ∀ j : ℤ, j < L → IsZero (J.X j))
    (hU : ∀ b : ℤ, b < M → IsZero (U.X b)) (hn : n < L + M) :
    IsZero ((complexAt R J U).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro j b hjb
  have hCell : IsZero (ModuleCat.tensorObjAt R (J.X j) (U.X b)) := by
    by_cases hj : j < L
    · exact ((ModuleCat.tensorBifunctorAt R).flip.obj (U.X b)).map_isZero (hJ j hj)
    · have hb : b < M := by change j + b = n at hjb; omega
      exact ((ModuleCat.tensorBifunctorAt R).obj (J.X j)).map_isZero (hU b hb)
  exact hCell.eq_of_src _ _

/-- Every original right-hand Hom coordinate outside its finite interval is zero. -/
theorem homTensor_right_coordinate_zero
    (P J U : CochainComplex (ModuleCat.{v} R) ℤ) (N L M n p q : ℤ)
    (hP : ∀ p : ℤ, N < p → IsZero (P.X p))
    (hJ : ∀ j : ℤ, j < L → IsZero (J.X j))
    (hU : ∀ b : ℤ, b < M → IsZero (U.X b))
    (hpn : p + n = q) (hp : p < L + M - n ∨ N < p)
    (z : Cochain P (complexAt R J U) n) : z.v p q hpn = 0 := by
  rcases hp with hp | hp
  · have hq : q < L + M := by omega
    exact (complexAt_isZero_X_of_lower_bounds R J U L M q hJ hU hq).eq_of_tgt _ _
  · exact (hP p hp).eq_of_src _ _

end CochainComplex.ModuleTensor
