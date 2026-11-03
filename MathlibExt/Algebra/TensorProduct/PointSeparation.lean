/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The theorem statement is adapted from
`Theorems/Thm_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero.lean`
and its paired `P2M/Sol/S_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
The proof below uses tensor coordinates instead of the source's double basis sum;
it does not require the source's finite-dimensionality assumption.
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Separation of tensors by pairs of algebraic points

If a family of points separates the scalar extension of an algebra, pairs of
those points separate its tensor square. Neither the point index nor the
algebra's dimension is required to be finite.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {K L A P : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing A] [Algebra K A] (pt : P → A →ₐ[K] L)

private theorem eq_zero_of_forall_point_eq_zero
    (hinj : Function.Injective
      (lift (Algebra.ofId L (P → L)) (AlgHom.pi pt)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (a : A) (ha : ∀ p, pt p a = 0) : a = 0 := by
  apply includeRight_injective (A := L) (algebraMap K L).injective
  apply hinj
  ext p
  simpa using ha p

/-- If the scalar-extended evaluation map is injective, a tensor vanishing at
all pairs of selected algebraic points is zero. The algebra and the point
index may be infinite; no closedness or perfection assumption is needed. -/
theorem eq_zero_of_forall_lift_apply_eq_zero
    (hinj : Function.Injective
      (lift (Algebra.ofId L (P → L)) (AlgHom.pi pt)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (x : A ⊗[K] A)
    (hx : ∀ p q, lift (pt p) (pt q) (fun _ _ => Commute.all _ _) x = 0) : x = 0 := by
  classical
  let ev : L ⊗[K] A →ₐ[L] (P → L) :=
    lift (Algebra.ofId L (P → L)) (AlgHom.pi pt) (fun _ _ => Commute.all _ _)
  have hs (p : P) : map (pt p) (AlgHom.id K A) x = 0 := by
    apply hinj
    ext q
    have he (y : A ⊗[K] A) :
        ev (map (pt p) (AlgHom.id K A) y) q =
          lift (pt p) (pt q) (fun _ _ => Commute.all _ _) y := by
      induction y using TensorProduct.inductionOn with
      | tmul a b => simp [ev]
      | add y z hy hz => simp [map_add, hy, hz]
    simpa using (he x).trans (hx p q)
  let b := Module.Free.chooseBasis K A
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  apply eq_zero_of_forall_point_eq_zero pt hinj
  intro p
  have he (y : A ⊗[K] A) :
      TensorProduct.equivFinsuppOfBasisRight b (map (pt p) (AlgHom.id K A) y) i =
        pt p (TensorProduct.equivFinsuppOfBasisRight b y i) := by
    induction y using TensorProduct.inductionOn with
    | tmul a a' => simp
    | add y z hy hz => simp [map_add, hy, hz]
  rw [← he, hs]
  simp

end Algebra.TensorProduct
