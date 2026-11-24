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
# Actual Eulerian cyclic norm actions on original tensor powers

The actual rational permutation representation sends the original signed
cyclic norm to the existing native tensor norm. The actual head-fixing
group-ring embedding acts through the original first/tail tensor coordinates.
Mapping the proved cyclic coefficient identity therefore gives the concrete
operator identity at two, without a caller-supplied norm equation.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v

namespace TensorPower

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]

/-- The actual rational coefficient image of the native tail representation. -/
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

/-- The original group-ring cyclic norm has exactly the existing native signed tensor norm action. -/
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

/-- The actual head-fixed rational group-ring action is the original tensor extension of its tail action. -/
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

/-- The actual convolution-at-two operator and the original tensor norm have the exact head-fixed identity. -/
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
