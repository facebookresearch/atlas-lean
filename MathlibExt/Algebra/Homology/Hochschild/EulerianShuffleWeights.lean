/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.RationalEulerianComplex

/-!
# Eulerian weights of coefficient shuffle products

Let k be a commutative ℚ-algebra, A a commutative unital k-algebra,
and M a compatible symmetric A-bimodule. The shuffle pairing
C_p(A,U^wA)⊗C_q(A,M)→C_{p+q}(A,M)
intertwines the bar-lambda convolution at two.

If the two inputs have Eulerian weights i,j, their shuffle product
has eigenvalue 2^{i+j} for that convolution. Every projector onto
weight r≠i+j kills it, and the weight-(i+j) projector fixes it.
Thus the product of weight-i and weight-j range elements belongs to
the weight-(i+j) range, for all p,q,i,j≥0.

Reference: J.-L. Loday, Cyclic Homology, §4.5.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

private theorem twoPow_injective : Function.Injective (fun n : ℕ => (2 : ℚ) ^ n) := by
  apply StrictMono.injective
  apply strictMono_nat_of_lt_succ
  intro n
  rw [pow_succ]
  have hp : (0 : ℚ) < 2 ^ n := pow_pos (by norm_num) n
  nlinarith

/-- Let k be a commutative ℚ-algebra, A a commutative unital
k-algebra, and M a compatible A-module regarded as a symmetric bimodule.
The coefficient shuffle pairs C_p(A,U^wA) with C_q(A,M)
in the common k-module universe max{u,v,w}.
Writing Sh_{p,q} for the coefficient shuffle pairing and Λ for
bar-lambda at two, the square is
Λ_{p+q}Sh_{p,q}=Sh_{p,q}(Λ_p⊗Λ_q). -/
theorem lambdaTwo_coefficientShufflePairingMap (p q : ℕ) :
    (lambdaTwoOperator k A M (p + q)).comp (coefficientShufflePairingMap k A M p q) =
      (coefficientShufflePairingMap k A M p q).comp
        (TensorProduct.map (lambdaTwoOperator k A (ULift.{w} A) p) (lambdaTwoOperator k A M q)) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  have h := lambdaTwo_pairing k A M p q
  simp only [pairing_pair_eq_coefficientShuffleMap] at h
  exact h

private theorem paired_eigenvalue
    {P Q T : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
    [Module k P] [Module k Q] [Module k T]
    (L : T →ₗ[k] T) (C : P ⊗[k] Q →ₗ[k] T)
    (LP EP : P →ₗ[k] P) (LQ EQ : Q →ₗ[k] Q) (a b : k)
    (hL : L.comp C = C.comp (TensorProduct.map LP LQ))
    (hP : LP.comp EP = a • EP) (hQ : LQ.comp EQ = b • EQ) :
    L.comp (C.comp (TensorProduct.map EP EQ)) =
      (a * b) • C.comp (TensorProduct.map EP EQ) := by
  have h := congrArg (fun f => f.comp (TensorProduct.map EP EQ)) hL
  simp only [LinearMap.comp_assoc] at h
  rw [← TensorProduct.map_comp, hP, hQ,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right] at h
  simpa only [LinearMap.comp_smul, smul_smul] using h

/-- Let k be a commutative ℚ-algebra, A a commutative unital
k-algebra, and M a compatible A-module regarded as a symmetric bimodule.
The coefficient shuffle pairs C_p(A,U^wA) with C_q(A,M)
in the common k-module universe max{u,v,w}.
For the projected product Sh_{p,q}(e_p^{(i)}⊗e_q^{(j)}),
the convolution eigenvalue is 2^{i+j}:
Λ_{p+q}Sh(e_i⊗e_j)=algMap_ℚ(2^{i+j})Sh(e_i⊗e_j). -/
theorem coefficientShuffle_projected_eigenvalue (p q i j : ℕ) :
    (lambdaTwoOperator k A M (p + q)).comp
        ((coefficientShufflePairingMap k A M p q).comp
          (TensorProduct.map (coefficientEulerianOperator k A (ULift.{w} A) p i)
            (coefficientEulerianOperator k A M q j))) =
      algebraMap ℚ k ((2 : ℚ) ^ (i + j)) •
        (coefficientShufflePairingMap k A M p q).comp
          (TensorProduct.map (coefficientEulerianOperator k A (ULift.{w} A) p i)
            (coefficientEulerianOperator k A M q j)) := by
  by_cases hi : i ≤ p
  · by_cases hj : j ≤ q
    · have h := paired_eigenvalue k
        (lambdaTwoOperator k A M (p + q)) (coefficientShufflePairingMap k A M p q)
        (lambdaTwoOperator k A (ULift.{w} A) p) (coefficientEulerianOperator k A (ULift.{w} A) p i)
        (lambdaTwoOperator k A M q) (coefficientEulerianOperator k A M q j)
        (algebraMap ℚ k ((2 : ℚ) ^ i)) (algebraMap ℚ k ((2 : ℚ) ^ j))
        (lambdaTwo_coefficientShufflePairingMap k A M p q)
        (lambdaTwo_comp_eulerian k A (ULift.{w} A) p i hi)
        (lambdaTwo_comp_eulerian k A M q j hj)
      simpa only [← map_mul, ← pow_add] using h
    · rw [coefficientEulerian_outside k A M q j (by omega), TensorProduct.map_zero_right,
        LinearMap.comp_zero, LinearMap.comp_zero, smul_zero]
  · rw [coefficientEulerian_outside k A (ULift.{w} A) p i (by omega), TensorProduct.map_zero_left,
      LinearMap.comp_zero, LinearMap.comp_zero, smul_zero]

/-- Let k be a commutative ℚ-algebra, A a commutative unital
k-algebra, and M a compatible A-module regarded as a symmetric bimodule.
The coefficient shuffle pairs C_p(A,U^wA) with C_q(A,M)
in the common k-module universe max{u,v,w}.
If r≠i+j, then e_{p+q}^{(r)}Sh_{p,q}(e_p^{(i)}⊗e_q^{(j)})=0. -/
theorem coefficientShuffle_projected_cross_zero (p q i j r : ℕ) (hr : r ≠ i + j) :
    (coefficientEulerianOperator k A M (p + q) r).comp
      ((coefficientShufflePairingMap k A M p q).comp
        (TensorProduct.map (coefficientEulerianOperator k A (ULift.{w} A) p i)
          (coefficientEulerianOperator k A M q j))) = 0 := by
  by_cases hs : r ≤ p + q
  · let X := (coefficientShufflePairingMap k A M p q).comp
      (TensorProduct.map (coefficientEulerianOperator k A (ULift.{w} A) p i)
        (coefficientEulerianOperator k A M q j))
    let Y := (coefficientEulerianOperator k A M (p + q) r).comp X
    have h := congrArg (fun f => (coefficientEulerianOperator k A M (p + q) r).comp f)
      (coefficientShuffle_projected_eigenvalue k A M p q i j)
    rw [← LinearMap.comp_assoc, eulerian_comp_lambdaTwo k A M (p + q) r hs] at h
    simp only [LinearMap.comp_smul, LinearMap.smul_comp] at h
    have hz : algebraMap ℚ k ((2 : ℚ) ^ r - (2 : ℚ) ^ (i + j)) • Y = 0 := by
      have hY : algebraMap ℚ k ((2 : ℚ) ^ r) • Y =
          algebraMap ℚ k ((2 : ℚ) ^ (i + j)) • Y := h
      exact (congrArg (fun c : k => c • Y) (map_sub (algebraMap ℚ k) _ _)).trans
        ((sub_smul _ _ Y).trans (sub_eq_zero.mpr hY))
    have hneq : (2 : ℚ) ^ r - (2 : ℚ) ^ (i + j) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hr (twoPow_injective h))
    have hc := congrArg (fun Z =>
      algebraMap ℚ k (((2 : ℚ) ^ r - (2 : ℚ) ^ (i + j))⁻¹) • Z) hz
    simpa only [smul_smul, ← map_mul, inv_mul_cancel₀ hneq, map_one,
      one_smul, smul_zero, X, Y] using hc
  · rw [coefficientEulerian_outside k A M (p + q) r (by omega), LinearMap.zero_comp]

/-- Let k be a commutative ℚ-algebra, A a commutative unital
k-algebra, and M a compatible A-module regarded as a symmetric bimodule.
The coefficient shuffle pairs C_p(A,U^wA) with C_q(A,M)
in the common k-module universe max{u,v,w}.
The sum-weight projector fixes the projected product:
e_{p+q}^{(i+j)}Sh_{p,q}(e_p^{(i)}⊗e_q^{(j)})
=Sh_{p,q}(e_p^{(i)}⊗e_q^{(j)}). -/
theorem coefficientShuffle_projected_weight (p q i j : ℕ) :
    (coefficientEulerianOperator k A M (p + q) (i + j)).comp
      ((coefficientShufflePairingMap k A M p q).comp
        (TensorProduct.map (coefficientEulerianOperator k A (ULift.{w} A) p i)
          (coefficientEulerianOperator k A M q j))) =
      (coefficientShufflePairingMap k A M p q).comp
        (TensorProduct.map (coefficientEulerianOperator k A (ULift.{w} A) p i)
          (coefficientEulerianOperator k A M q j)) := by
  classical
  by_cases hi : i ≤ p
  · by_cases hj : j ≤ q
    · let X := (coefficientShufflePairingMap k A M p q).comp
        (TensorProduct.map (coefficientEulerianOperator k A (ULift.{w} A) p i)
          (coefficientEulerianOperator k A M q j))
      have hs : i + j ≤ p + q := Nat.add_le_add hi hj
      let r₀ : Fin (p + q + 1) := ⟨i + j, Nat.lt_succ_of_le hs⟩
      have h : X = (coefficientEulerianOperator k A M (p + q) (i + j)).comp X := by
        calc
          _ = (∑ r : Fin (p + q + 1), coefficientEulerianOperator k A M (p + q) r.val).comp X := by
            rw [(coefficientEulerian_projector_laws k A M (p + q)).1, LinearMap.id_comp]
          _ = ∑ r : Fin (p + q + 1), (coefficientEulerianOperator k A M (p + q) r.val).comp X := by
            apply LinearMap.ext
            intro z
            simp only [LinearMap.comp_apply, LinearMap.sum_apply]
          _ = _ := by
            have hsingle : (∑ r : Fin (p + q + 1),
                (coefficientEulerianOperator k A M (p + q) r.val).comp X) =
                (coefficientEulerianOperator k A M (p + q) r₀.val).comp X :=
              Finset.sum_eq_single r₀ (by
                intro r _ hne
                exact coefficientShuffle_projected_cross_zero k A M p q i j r.val
                  (fun he => hne (Fin.ext he))) (by simp)
            exact hsingle
      exact h.symm
    · rw [coefficientEulerian_outside k A M q j (by omega), TensorProduct.map_zero_right,
        LinearMap.comp_zero, LinearMap.comp_zero]
  · rw [coefficientEulerian_outside k A (ULift.{w} A) p i (by omega), TensorProduct.map_zero_left,
      LinearMap.comp_zero, LinearMap.comp_zero]

/-- Let k be a commutative ℚ-algebra, A a commutative unital
k-algebra, and M a compatible A-module regarded as a symmetric bimodule.
The coefficient shuffle pairs C_p(A,U^wA) with C_q(A,M)
in the common k-module universe max{u,v,w}.
If x lies in the weight-i range in degree p and y in the
weight-j range in degree q, then Sh_{p,q}(x⊗y) lies in
the weight-(i+j) range in degree p+q. -/
theorem coefficientShuffle_mem_weight (p q i j : ℕ)
    (x : ULift.{w} A ⊗[k] TensorPower k p A) (y : M ⊗[k] TensorPower k q A)
    (hx : x ∈ LinearMap.range (coefficientEulerianOperator k A (ULift.{w} A) p i))
    (hy : y ∈ LinearMap.range (coefficientEulerianOperator k A M q j)) :
    coefficientShufflePairingMap k A M p q (x ⊗ₜ[k] y) ∈
      LinearMap.range (coefficientEulerianOperator k A M (p + q) (i + j)) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨coefficientShufflePairingMap k A M p q
    (coefficientEulerianOperator k A (ULift.{w} A) p i a ⊗ₜ[k]
      coefficientEulerianOperator k A M q j b), ?_⟩
  have h := DFunLike.congr_fun (coefficientShuffle_projected_weight k A M p q i j) (a ⊗ₜ[k] b)
  simpa only [LinearMap.comp_apply, TensorProduct.map_tmul] using h

end ModuleCat.Algebra.Hochschild.Symmetric
