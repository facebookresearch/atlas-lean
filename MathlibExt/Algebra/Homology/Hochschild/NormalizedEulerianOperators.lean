/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianComplex
public import MathlibExt.Combinatorics.Perm.EulerianRationalFamily

/-!
# Normalized rational Eulerian operators

Rational permutation projectors act
on the coefficient-fixed ground quotient
tails. They have finite support,
orthogonality and completeness. The
quotient tails carry no algebra structure.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

local notation "Q" => ModuleCat.Algebra.Hochschild.quotientCarrier k A

/-- The coefficient-fixed Eulerian projector on original normalized tails. -/
def normalizedEulerianOperator (n i : ℕ) : Module.End k (M ⊗[k] TensorPower k n Q) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n (Equiv.Perm.eulerianElement n i)

/-- The normalized convolution parameter family fixes the original coefficient. -/
def normalizedConvolutionOperator (n : ℕ) (a : ℚ) : Module.End k (M ⊗[k] TensorPower k n Q) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n (Equiv.Perm.eulerianLambda n a)

/-- The normalized rational parameter operation has its original finite Eulerian expansion. -/
theorem normalizedConvolutionOperator_eq_sum (n : ℕ) (a : ℚ) :
    normalizedConvolutionOperator k A M n a =
      ∑ i : Fin (n + 1), algebraMap ℚ k (a ^ i.val) • normalizedEulerianOperator k A M n i.val := by
  rw [normalizedConvolutionOperator, Equiv.Perm.eulerianLambda_eq_sum, map_sum]
  simp only [TensorPower.coefficientRationalPermutationAction_smul, normalizedEulerianOperator]

/-- The normalized family is finite and complete in every original degree. -/
theorem normalizedEulerianOperator_sum (n : ℕ) :
    (∑ i : Fin (n + 1), normalizedEulerianOperator k A M n i.val) = LinearMap.id := by
  change (∑ i : Fin (n + 1),
    TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n (Equiv.Perm.eulerianElement n i.val)) = 1
  rw [← map_sum, (Equiv.Perm.eulerianElement_projector_laws n).1, map_one]

/-- Actual normalized Eulerian operators are orthogonal idempotents. -/
theorem normalizedEulerianOperator_comp (n i j : ℕ) :
    (normalizedEulerianOperator k A M n i).comp (normalizedEulerianOperator k A M n j) =
      if i = j then normalizedEulerianOperator k A M n i else 0 := by
  change TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianElement n i) *
    TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianElement n j) = _
  rw [← map_mul, (Equiv.Perm.eulerianElement_projector_laws n).2 i j]
  split_ifs
  · rfl
  · exact map_zero (TensorPower.coefficientRationalPermutationAction (k := k) (M := M) (V := Q) n)

/-- The normalized support is the original homogeneous tensor degree. -/
theorem normalizedEulerianOperator_outside (n i : ℕ) (h : n < i) :
    normalizedEulerianOperator k A M n i = 0 := by
  rw [normalizedEulerianOperator, Equiv.Perm.eulerianElement_outside n i h, map_zero]

/-- The normalized convolution has its original eigenvalue on each supported projector. -/
theorem normalizedConvolutionOperator_comp_eulerian
    (n i : ℕ) (h : i ≤ n) (a : ℚ) :
    (normalizedConvolutionOperator k A M n a).comp (normalizedEulerianOperator k A M n i) =
      algebraMap ℚ k (a ^ i) • normalizedEulerianOperator k A M n i := by
  change TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianLambda n a) *
    TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianElement n i) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul_eulerianElement n i h a,
    TensorPower.coefficientRationalPermutationAction_smul]
  rfl

/-- The normalized projector has the same eigenvalue on the other side of the convolution. -/
theorem normalizedEulerianOperator_comp_convolution
    (n i : ℕ) (h : i ≤ n) (a : ℚ) :
    (normalizedEulerianOperator k A M n i).comp (normalizedConvolutionOperator k A M n a) =
      algebraMap ℚ k (a ^ i) • normalizedEulerianOperator k A M n i := by
  classical
  let i₀ : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le h⟩
  rw [normalizedConvolutionOperator_eq_sum]
  have hsum : (normalizedEulerianOperator k A M n i).comp
      (∑ j : Fin (n + 1), algebraMap ℚ k (a ^ j.val) • normalizedEulerianOperator k A M n j.val) =
    ∑ j : Fin (n + 1), (normalizedEulerianOperator k A M n i).comp
      (algebraMap ℚ k (a ^ j.val) • normalizedEulerianOperator k A M n j.val) := by
    apply LinearMap.ext
    intro x
    have hmap := map_sum (normalizedEulerianOperator k A M n i)
      (fun j : Fin (n + 1) =>
        (algebraMap ℚ k (a ^ j.val) • normalizedEulerianOperator k A M n j.val) x) Finset.univ
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using hmap
  rw [hsum]
  simp only [LinearMap.comp_smul, normalizedEulerianOperator_comp]
  rw [Finset.sum_eq_single i₀]
  · simp [i₀]
  · intro j _ hj
    have hne : i ≠ j.val := fun he => hj (Fin.ext he.symm)
    simp only [hne, if_false, smul_zero]
  · simp

/-- The original normalized A-linear operator restricts to this same ground operator. -/
theorem algebraNormalizedEulerianOperator_eq_ground (n i : ℕ) :
    (algebraNormalizedEulerianOperator k A M n i).restrictScalars k =
      normalizedEulerianOperator k A M n i :=
  algebraNormalizedEulerianOperator_restrictScalars k A M n i

/-- The complete normalized boundary commutes with every original Eulerian projector. -/
theorem normalizedEulerianOperator_boundary (n i : ℕ) :
    ((normalizedChainComplex k A M).d (n + 1) n).hom.comp
        (normalizedEulerianOperator k A M (n + 1) i) =
      (normalizedEulerianOperator k A M n i).comp
        ((normalizedChainComplex k A M).d (n + 1) n).hom := by
  change ((algebraNormalizedBoundary k A M n).restrictScalars k).comp
      (normalizedEulerianOperator k A M (n + 1) i) =
    (normalizedEulerianOperator k A M n i).comp ((algebraNormalizedBoundary k A M n).restrictScalars k)
  have h := congrArg (fun f => f.restrictScalars k)
    (algebraNormalizedEulerianOperator_boundary k A M n i)
  simpa only [LinearMap.restrictScalars_comp, algebraNormalizedEulerianOperator_eq_ground] using h

/-- The original normalized coefficient projector is a native chain map. -/
def normalizedEulerianChainMap (i : ℕ) : normalizedChainComplex k A M ⟶ normalizedChainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (normalizedEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    exact normalizedEulerianOperator_boundary k A M n i)

end ModuleCat.Algebra.Hochschild.Symmetric
