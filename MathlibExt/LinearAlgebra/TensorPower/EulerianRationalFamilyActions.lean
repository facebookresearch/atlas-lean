/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianRationalFamily
public import MathlibExt.LinearAlgebra.TensorPower.PermutationShuffleActions

/-!
# Rational Eulerian convolution on coefficient tensors

Let k be a commutative ℚ-algebra and M,V k-modules. The Eulerian family Aₙ(a) on M ⊗ V⊗n is the
action of Λₙ(a) = ∑ᵢ₌₀ⁿ aⁱeₙ⁽ⁱ⁾, for a ∈ ℚ. It satisfies Aₙ(a)Aₙ(b) = Aₙ(ab), and Aₙ(a) is
invertible for a ≠ 0 with inverse Aₙ(a⁻¹). Coefficient maps and factorwise linear maps
intertwine these actions. On tensor powers the family also preserves the signed shuffle product.

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5, for the Eulerian decomposition and its
convolution family.
-/

@[expose] public section
noncomputable section

open scoped BigOperators TensorProduct

universe u v w v' w'

namespace TensorPower

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {W : Type v'} [AddCommGroup W] [Module k W]
  {M : Type w} [AddCommGroup M] [Module k M]
  {N : Type w'} [AddCommGroup N] [Module k N]

/-- Multiplication of rational Eulerian convolution operators.

For a commutative ℚ-algebra k and k-modules M,V, let Aₙ(a) be the action of Λₙ(a) on M ⊗
V⊗n. For a,b ∈ ℚ, Aₙ(a) ∘ Aₙ(b) = Aₙ(ab). -/
theorem coefficientEulerianLambda_mul (n : ℕ) (a b : ℚ) :
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
      a)).comp
        (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
          (Equiv.Perm.eulerianLambda n b)) =
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
        (a * b)) := by
  change coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
    (Equiv.Perm.eulerianLambda n a) *
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
      b) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul]

/-- The eigenvalue on an Eulerian summand.

For a commutative ℚ-algebra k, k-modules M,V, i ≤ n and a ∈ ℚ, the action Aₙ(a) composed
with the projector eₙ⁽ⁱ⁾ equals algebraMap(aⁱ) times that projector on M ⊗ V⊗n. -/
theorem coefficientEulerianLambda_comp_eulerian (n i : ℕ) (hi : i ≤ n) (a : ℚ) :
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
      a)).comp
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianElement
        n i)) =
    algebraMap ℚ k (a ^ i) • coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.eulerianElement n i) := by
  change coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
    (Equiv.Perm.eulerianLambda n a) *
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianElement n
      i) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul_eulerianElement n i hi a,
    coefficientRationalPermutationAction_smul]

/-- The Eulerian convolution equivalence at a nonzero parameter.

For a commutative ℚ-algebra k, k-modules M,V and a ≠ 0 in ℚ, Aₙ(a) defines a k-linear
equivalence of M ⊗ V⊗n. Its inverse is Aₙ(a⁻¹). -/
def coefficientEulerianLambdaEquiv (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    M ⊗[k] TensorPower k n V ≃ₗ[k] M ⊗[k] TensorPower k n V :=
  LinearEquiv.ofLinearMap
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
      a))
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
      a⁻¹))
    (by rw [coefficientEulerianLambda_mul (k := k) (M := M) (V := V), mul_inv_cancel₀ ha,
      Equiv.Perm.eulerianLambda_one, map_one]; rfl)
    (by rw [coefficientEulerianLambda_mul (k := k) (M := M) (V := V), inv_mul_cancel₀ ha,
      Equiv.Perm.eulerianLambda_one, map_one]; rfl)

/-- The forward map of the convolution equivalence.

For a commutative ℚ-algebra k, k-modules M,V and a ≠ 0 in ℚ, the linear map underlying
coefficientEulerianLambdaEquiv is the action of Λₙ(a) on M ⊗ V⊗n. -/
theorem coefficientEulerianLambdaEquiv_toLinearMap (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (coefficientEulerianLambdaEquiv (k := k) (M := M) (V := V) n a ha).toLinearMap =
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
        a) := rfl

/-- The inverse map of the convolution equivalence.

For a commutative ℚ-algebra k, k-modules M,V and a ≠ 0 in ℚ, the inverse linear map is the
action of Λₙ(a⁻¹) on M ⊗ V⊗n. -/
theorem coefficientEulerianLambdaEquiv_symm_toLinearMap (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (coefficientEulerianLambdaEquiv (k := k) (M := M) (V := V) n a ha).symm.toLinearMap =
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n
        a⁻¹) := rfl

/-- Naturality of Eulerian convolution in coefficients and tensor factors.

For a commutative ℚ-algebra k and k-linear maps f : M → N and g : V → W, put T = f ⊗ g⊗n.
Then T ∘ Aₙ,M,V(a) = Aₙ,N,W(a) ∘ T for every a ∈ ℚ. The four modules may have independent
universes. -/
theorem coefficientEulerianLambda_naturality (n : ℕ) (a : ℚ) (f : M →ₗ[k] N) (g : V →ₗ[k] W) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))).comp
        (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
          (Equiv.Perm.eulerianLambda n a)) =
      (coefficientRationalPermutationAction (k := k) (M := N) (V := W) n (Equiv.Perm.eulerianLambda
        n a)).comp
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  rw [Equiv.Perm.eulerianLambda, coefficientRationalPermutationAction_sum,
    coefficientRationalPermutationAction_sum]
  exact coefficientPermutationOperator_naturality n _ g f

/-- Eulerian convolution preserves the signed shuffle product.

For a commutative ℚ-algebra k, a k-module V, p,q ≥ 0 and a ∈ ℚ, let shₚ,ᵩ : V⊗p ⊗ V⊗q →
V⊗(p+q) be the shuffle product weighted by permutation signs. Then Aₚ₊ᵩ(a) ∘ shₚ,ᵩ = shₚ,ᵩ ∘
(Aₚ(a) ⊗ Aᵩ(a)). -/
theorem rationalEulerianLambda_signedShuffleProduct_rat (p q : ℕ) (a : ℚ) :
    (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.eulerianLambda (p + q) a)).comp
        (signedShuffleProduct (k := k) (V := V) p q) =
      (signedShuffleProduct (k := k) (V := V) p q).comp (TensorProduct.map
        (rationalPermutationAction (k := k) (V := V) p (Equiv.Perm.eulerianLambda p a))
        (rationalPermutationAction (k := k) (V := V) q (Equiv.Perm.eulerianLambda q a))) := by
  have h := congrArg (rationalPermutationAction (k := k) (V := V) (p + q))
    (Equiv.Perm.eulerianLambda_mul_signedShuffle_rat p q a)
  rw [map_mul, map_mul, rationalPermutationAction_signedShuffle] at h
  change (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.eulerianLambda (p + q)
    a)).comp
      (signedShuffleEnd (k := k) (V := V) p q) = (signedShuffleEnd (k := k) (V := V) p q).comp
    (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.splitEulerianLambda p q a)) at
      h
  have hcomp := congrArg (fun f => f.comp
    (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap) h
  simpa only [signedShuffleProduct, LinearMap.comp_assoc,
    rationalPermutationAction_splitEulerianLambda] using hcomp

end TensorPower
