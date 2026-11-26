/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.EulerianCyclicNorm
public import MathlibExt.LinearAlgebra.TensorPower.PermutationShuffleActions
public import MathlibExt.LinearAlgebra.TensorPower.Cyclic
public import MathlibExt.LinearAlgebra.TensorPower.HeadFixingAction

/-!
# Eulerian convolution and the cyclic norm

Let k be a commutative ℚ-algebra and V a k-module. On V⊗(n+1), the signed cyclic operator is tₙ
= (-1)ⁿρ(finRotate(n+1)), and its norm is Nₙ = ∑ᵣ₌₀ⁿ tₙʳ. The rational permutation action sends
the signed cyclic norm element to Nₙ. Writing h for the embedding that fixes the first tensor
factor, the convolution identity at two is Λₙ₊₁(2)Nₙ = 2Nₙh(Λₙ(2)).

For cyclic norms and Eulerian operations, see J.-L. Loday, Cyclic Homology, 2nd ed., Chapter 1
and §4.5.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v

namespace TensorPower

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]

/-- Scalar compatibility of the rational permutation action.

For a commutative ℚ-algebra k, a k-module V, c ∈ ℚ and x ∈ ℚ[Sₙ], the action satisfies ρₙ(c
x) = algebraMap(c) · ρₙ(x) on V⊗n. -/
theorem rationalPermutationAction_smul (n : ℕ) (c : ℚ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    rationalPermutationAction (k := k) (V := V) n (c • x) =
      algebraMap ℚ k c • rationalPermutationAction (k := k) (V := V) n x := by
  let ρ := rationalPermutationAction (k := k) (V := V) n
  rw [Algebra.smul_def, map_mul]
  have hc : ρ (algebraMap ℚ (MonoidAlgebra ℚ (Equiv.Perm (Fin n))) c) =
      algebraMap ℚ k c • (1 : Module.End k (TensorPower k n V)) := by
    change rationalPermutationAction (k := k) (V := V) n (MonoidAlgebra.single 1 c) = _
    rw [rationalPermutationAction_single, map_one]
  rw [hc, smul_mul_assoc, _root_.one_mul]

/-- The signed cyclic norm acts as the tensor norm.

For a commutative ℚ-algebra k and a k-module V, the action of ∑ᵣ₌₀ⁿ
sign(finRotate(n+1)ʳ)[finRotate(n+1)ʳ] equals Nₙ = ∑ᵣ₌₀ⁿ tₙʳ on V⊗(n+1), with tₙ =
(-1)ⁿρ(finRotate(n+1)). -/
theorem rationalPermutationAction_cyclicNorm (n : ℕ) :
    rationalPermutationAction (k := k) (V := V) (n + 1) (Equiv.Perm.signedCyclicNormElement ℚ n) =
      norm k V n := by
  classical
  rw [Equiv.Perm.signedCyclicNormElement, map_sum]
  simp_rw [rationalPermutationAction_single]
  rw [norm, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  change (algebraMap ℚ k (((((finRotate (n + 1) ^ r.val).sign : ℤ) : ℚ)))) •
      PiTensorProduct.reindex k (fun _ : Fin (n + 1) => V) (finRotate (n + 1) ^ r.val)
        (PiTensorProduct.tprod k a) =
    (cyclicOperator k V n ^ r.val) (PiTensorProduct.tprod k a)
  simp only [PiTensorProduct.reindex_tprod, cyclicOperator_pow_tprod]
  have hs : algebraMap ℚ k
      (((((finRotate (n + 1) ^ r.val).sign : ℤ) : ℚ))) = (-1 : k) ^ (n * r.val) := by
    have hsign : (finRotate (n + 1) ^ r.val).sign = (finRotate (n + 1)).sign ^ r.val :=
      map_pow Equiv.Perm.sign (finRotate (n + 1)) r.val
    rw [hsign, _root_.sign_finRotate]
    simp only [Nat.add_sub_cancel, ← pow_mul, Units.val_pow_eq_pow_val,
      Units.coe_neg_one, Int.cast_pow, Int.cast_neg, Int.cast_one, map_pow,
      map_neg, map_one]
  rw [hs]

/-- The head-fixed action in first-factor tensor coordinates.

For a commutative ℚ-algebra k, a k-module V and x ∈ ℚ[Sₙ], the action of h(x) on V⊗(n+1)
corresponds, under consEquiv : V ⊗ V⊗n ≃ V⊗(n+1), to id_V ⊗ ρₙ(x). -/
theorem rationalPermutationAction_headFixing_cons (n : ℕ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    (rationalPermutationAction (k := k) (V := V) (n + 1)
      (Equiv.Perm.headFixingGroupRingMap ℚ n x)).comp (consEquiv k V n).toLinearMap =
      (consEquiv k V n).toLinearMap.comp
        (TensorProduct.map LinearMap.id (rationalPermutationAction (k := k) (V := V) n x)) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_comp, TensorProduct.map_zero_right,
      LinearMap.comp_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_comp, TensorProduct.map_add_right,
      LinearMap.comp_add, hx, hy]
  | single σ c =>
    rw [Equiv.Perm.headFixingGroupRingMap_single, rationalPermutationAction_single,
      rationalPermutationAction_single, LinearMap.smul_comp, TensorProduct.map_smul_right,
      LinearMap.comp_smul]
    rw [permutationRepresentation_headFixing_cons]

/-- The convolution-at-two identity for the cyclic norm.

For a commutative ℚ-algebra k and a k-module V, Λₙ₊₁(2) ∘ Nₙ = 2 · Nₙ ∘ ρₙ₊₁(h(Λₙ(2))). Here
Nₙ is the signed cyclic norm on V⊗(n+1), and h fixes the first tensor factor. -/
theorem rationalEulerianLambda_two_cyclicNorm (n : ℕ) :
    (rationalPermutationAction (k := k) (V := V) (n + 1) (Equiv.Perm.eulerianLambda (n + 1) 2)).comp
        (norm k V n) =
      (2 : k) • (norm k V n).comp
        (rationalPermutationAction (k := k) (V := V) (n + 1)
          (Equiv.Perm.headFixingGroupRingMap ℚ n (Equiv.Perm.eulerianLambda n 2))) := by
  have h := congrArg (rationalPermutationAction (k := k) (V := V) (n + 1))
    (Equiv.Perm.eulerianLambda_two_norm n)
  rw [map_mul, rationalPermutationAction_cyclicNorm, rationalPermutationAction_smul,
    map_mul, rationalPermutationAction_cyclicNorm] at h
  simpa only [map_ofNat, Module.End.mul_eq_comp] using h

end TensorPower
