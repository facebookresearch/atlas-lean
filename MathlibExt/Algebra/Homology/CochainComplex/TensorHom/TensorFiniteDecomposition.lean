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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.FiniteCoordinates
public import Mathlib.Data.Int.Interval

/-!
# Finite cell decompositions of tensor-total degrees

In a cochain tensor total, the cell of factor degree `b` in total degree `q` is `J^(q-b) ⊗
U^b`. If all nonzero cells occur in a finite set of such degrees, the identity of the total
object is the sum of the cell projections followed by their coprojections.

When `U` vanishes below `L` and above `N`, the finite set can be `[L, N]`, with no support
restriction on `J`. These identities use the same direct-sum total objects.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Tensor-total identity is a finite sum of cell projection and reinclusion.

If the cell `J^(q-b) ⊗ U^b` is zero for every `b` outside a finite set `s`, then the identity
in total degree `q` is `∑ b ∈ s, π_b ≫ ι_b` for its tensor-cell projections and coprojections. -/
theorem tensorDegree_id_eq_sum_of_support
    (J U : CochainComplex (ModuleCat.{v} R) ℤ) (q : ℤ) (s : Finset ℤ)
    (hCell : ∀ b : ℤ, b ∉ s →
      IsZero (ModuleCat.tensorObjAt R (J.X (q - b)) (U.X b))) :
    𝟙 ((complexAt R J U).X q) =
      ∑ b ∈ s, tensorCellProjection R J U (q - b) b q ≫
        HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
          (q - b) b q (by change q - b + b = q; omega) := by
  let K := complexAt R J U
  let i (b : ℤ) : ModuleCat.tensorObjAt R (J.X (q - b)) (U.X b) ⟶ K.X q :=
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
      (q - b) b q (by change q - b + b = q; omega)
  change 𝟙 (K.X q) = ∑ b ∈ s, tensorCellProjection R J U (q - b) b q ≫ i b
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro j b hjb
  have hj : j = q - b := by change j + b = q at hjb; omega
  subst hj
  change i b ≫ 𝟙 (K.X q) = i b ≫ ∑ k ∈ s,
    tensorCellProjection R J U (q - k) k q ≫ i k
  by_cases hb : b ∈ s
  · rw [Category.comp_id, Preadditive.comp_sum]
    symm
    calc
      _ = i b ≫ (tensorCellProjection R J U (q - b) b q ≫ i b) := by
        apply Finset.sum_eq_single b
        · intro k hk hkb
          have hz : i b ≫ tensorCellProjection R J U (q - k) k q = 0 :=
            tensorCellProjection_ι_eq_zero R J U (q - k) k q (q - b) b hjb
              (Or.inr hkb.symm)
          rw [← Category.assoc, hz, zero_comp]
        · intro h
          exact False.elim (h hb)
      _ = i b := by
        have hi : i b ≫ tensorCellProjection R J U (q - b) b q = 𝟙 _ :=
          tensorCellProjection_ι R J U (q - b) b q hjb
        rw [← Category.assoc, hi, Category.id_comp]
  · exact (hCell b hb).eq_of_src _ _

/-- Bounded right factor gives the finite tensor-cell identity decomposition.

If `U^b` vanishes below `L` and above `N`, then in every total degree `q`, the identity is the
sum of cell projection followed by reinclusion over `b ∈ Finset.Icc L N`. -/
theorem tensorDegree_id_eq_sum_of_bounded_right
    (J U : CochainComplex (ModuleCat.{v} R) ℤ) (L N q : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) :
    𝟙 ((complexAt R J U).X q) =
      ∑ b ∈ Finset.Icc L N, tensorCellProjection R J U (q - b) b q ≫
        HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
          (q - b) b q (by change q - b + b = q; omega) := by
  apply tensorDegree_id_eq_sum_of_support R J U q (Finset.Icc L N)
  intro b hb
  have hz : IsZero (U.X b) := by
    by_cases h : b < L
    · exact hUlo b h
    · have h' : N < b := by
        simp only [Finset.mem_Icc] at hb
        omega
      exact hUhi b h'
  exact ((ModuleCat.tensorBifunctorAt R).obj (J.X (q - b))).map_isZero hz

end CochainComplex.ModuleTensor
