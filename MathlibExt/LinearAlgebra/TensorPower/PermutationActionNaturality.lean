/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.LinearAlgebra.TensorPower.PermutationRepresentation

/-!
# Naturality of coefficient permutation actions

Let k be a commutative ring, M,N,V,W k-modules, and f : M → N, g : V → W k-linear maps. The map
T = f ⊗ g⊗n intertwines the actions of every x ∈ k[Sₙ] on the coefficient tensor modules. If k
is a ℚ-algebra, the same identity holds for x ∈ ℚ[Sₙ] after extending its coefficients to k. All
four modules may have independent universes.

This follows from tensor functoriality; see N. Bourbaki, Algebra I, Chapter III.
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

/-- Naturality of a group-algebra action on coefficient tensors.

For a commutative ring k, k-linear maps f : M → N and g : V → W, and x ∈ k[Sₙ], T = f ⊗ g⊗n
satisfies T ∘ ρₙ,M,V(x) = ρₙ,N,W(x) ∘ T. Each permutation fixes the coefficient factor. -/
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
  rw [hx, coefficientPermutationGroupAlgebraAction_sum,
    coefficientPermutationGroupAlgebraAction_sum]
  exact coefficientPermutationOperator_naturality n (fun σ => x.coeff σ) g f

variable [Algebra ℚ k]

/-- Naturality of the rational permutation action.

For a commutative ℚ-algebra k, k-linear maps f : M → N and g : V → W, and x ∈ ℚ[Sₙ], T = f ⊗
g⊗n intertwines the two actions of x after scalar extension to k. The modules may lie in
independent universes. -/
theorem coefficientRationalPermutationAction_naturality (n : ℕ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) (g : V →ₗ[k] W) (f : M →ₗ[k] N) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))).comp
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n x) =
        (coefficientRationalPermutationAction (k := k) (M := N) (V := W) n x).comp
          (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  exact coefficientPermutationGroupAlgebraAction_naturality n
    ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k)) x) g f

end TensorPower
