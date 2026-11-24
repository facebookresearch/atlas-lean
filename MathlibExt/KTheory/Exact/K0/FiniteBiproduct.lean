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

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import MathlibExt.KTheory.Exact.K0.Basic

/-!+# Finite biproduct classes in algebraic K₀

The class of an actual finite biproduct is the sum of the classes of its
summands. In particular, a finite biproduct of copies of one object has class
equal to its cardinality times that object's class.
-/

@[expose] public section

open CategoryTheory Limits

universe v u w

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [HasFiniteBiproducts C]

private noncomputable def finBiproductSuccIso {n : ℕ} (f : Fin (n + 1) → C) :
    (⨁ f) ≅ f 0 ⊞ ⨁ (fun i : Fin n => f i.succ) :=
  (biproduct.isLimit f).conePointUniqueUpToIso
    (extendFanIsLimit f
      (biproduct.isLimit (fun i : Fin n => f i.succ))
      (BinaryBiproduct.isLimit (f 0) (⨁ fun i : Fin n => f i.succ)))

/-- The class of a biproduct indexed by `Fin n` is the sum of its summand classes. -/
theorem K0.mk_biproduct_fin (n : ℕ) (f : Fin n → C) :
    K0.mk (⨁ f) = ∑ i, K0.mk (f i) := by
  induction n with
  | zero =>
      have hz : IsZero (⨁ f) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      simpa only [Finset.univ_eq_empty, Finset.sum_empty] using K0.mk_eq_zero_of_isZero hz
  | succ n ih =>
      rw [K0.mk_congr_of_iso (finBiproductSuccIso f), K0.mk_biprod,
        ih (fun i => f i.succ), Fin.sum_univ_succ]

/-- The class of a finite biproduct is the sum of the classes of the original family. -/
theorem K0.mk_biproduct {ι : Type w} [Fintype ι] (f : ι → C) :
    K0.mk (⨁ f) = ∑ i, K0.mk (f i) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let g : Fin (Fintype.card ι) → C := fun i => f (e.symm i)
  have he : (⨁ f) ≅ ⨁ g :=
    biproduct.whiskerEquiv e (fun i => eqToIso (congrArg f (e.symm_apply_apply i)))
  rw [K0.mk_congr_of_iso he, K0.mk_biproduct_fin]
  exact Fintype.sum_equiv e.symm (fun i => K0.mk (g i)) (fun i => K0.mk (f i))
    (fun _ => rfl)

/-- A finite biproduct of copies of one object represents its cardinal multiple in `K₀`. -/
theorem K0.mk_biproduct_const {ι : Type w} [Fintype ι] (X : C) :
    K0.mk (⨁ fun _ : ι => X) = Fintype.card ι • K0.mk X := by
  rw [K0.mk_biproduct]
  exact Finset.sum_const _

end AlgebraicKTheory
