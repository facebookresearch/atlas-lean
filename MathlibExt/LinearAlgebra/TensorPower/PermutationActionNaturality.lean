/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.LinearAlgebra.TensorPower.PermutationRepresentation

/-!
# Native coefficient group-algebra action across independent worlds

The original neutral permutation naturality applies to every actual
group-algebra element, by its finite coefficient expansion. Original
coefficient maps and uniform tail maps may have independent universes.
The rational specialization only changes the coefficient ring through its
actual ground map; no rational premise is attached to the neutral law.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w z t

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {W : Type w} [AddCommGroup W] [Module k W]
  {M : Type z} [AddCommGroup M] [Module k M]
  {N : Type t} [AddCommGroup N] [Module k N]

/-- Every group-algebra action commutes with original independent coefficient and tail maps. -/
theorem coefficientPermutationGroupAlgebraAction_naturality (n : ℕ)
    (x : MonoidAlgebra k (Equiv.Perm (Fin n))) (g : V →ₗ[k] W) (f : M →ₗ[k] N) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))).comp
      (coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n x) =
        (coefficientPermutationGroupAlgebraAction (k := k) (M := N) (V := W) n x).comp
          (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  classical
  have hx : x = ∑ σ : Equiv.Perm (Fin n), MonoidAlgebra.single σ (x.coeff σ) := by
    ext σ
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hx, coefficientPermutationGroupAlgebraAction_sum, coefficientPermutationGroupAlgebraAction_sum]
  exact coefficientPermutationOperator_naturality n (fun σ => x.coeff σ) g f

variable [Algebra ℚ k]

/-- Actual rational coefficient action is natural across the original independent coefficient and tail worlds. -/
theorem coefficientRationalPermutationAction_naturality (n : ℕ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) (g : V →ₗ[k] W) (f : M →ₗ[k] N) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))).comp
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n x) =
        (coefficientRationalPermutationAction (k := k) (M := N) (V := W) n x).comp
          (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  exact coefficientPermutationGroupAlgebraAction_naturality n
    ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k)) x) g f

end TensorPower
