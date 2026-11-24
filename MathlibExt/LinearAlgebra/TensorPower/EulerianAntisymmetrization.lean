/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.LinearAlgebra.TensorPower.ExteriorPermutationAction
public import MathlibExt.Combinatorics.Perm.EulerianProjectors
public import MathlibExt.Combinatorics.Perm.EulerianRationalFamily

/-!
# Actual Eulerian action on full exterior antisymmetrization

The neutral actual sign action gives the factorial norm on the entire
original exterior image. The rational top projector therefore
fixes that image, and orthogonality kills the other weights in every degree.
No freeness or flatness is used; the rational premise belongs to the actual
Eulerian coefficients, and no characteristic free isomorphism is inferred
from the factorial composite.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (V : Type v) [AddCommGroup V] [Module k V]
  (M : Type w) [AddCommGroup M] [Module k M]

/-- An original rational group-ring generator has its actual coefficient-fixed place action. -/
theorem coefficientRationalPermutationAction_single (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (c : ℚ) :
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (MonoidAlgebra.single σ c) =
      algebraMap ℚ k c • coefficientPermutationRepresentation (k := k) (M := M) (V := V) n σ := by
  change coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
    ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))
      (MonoidAlgebra.single σ c)) = _
  rw [MonoidAlgebra.mapRingHom_single, coefficientPermutationGroupAlgebraAction_single]

/-- The actual highest Eulerian projector fixes the entire original signed exterior image. -/
theorem coefficientEulerian_top_exteriorAntisymmetrization (n : ℕ) :
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.eulerianElement n n)).comp
        (TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n)) =
          TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n) := by
  classical
  let F := TensorProduct.map (LinearMap.id : M →ₗ[k] M) (exteriorAntisymmetrization k V n)
  have hsign (σ : Equiv.Perm (Fin n)) : (σ.sign : ℤ) * (σ.sign : ℤ) = 1 := by
    have hunit : σ.sign * σ.sign = 1 := by
      calc
        _ = (σ.sign)⁻¹ * σ.sign := by rw [Int.units_inv_eq_self]
        _ = 1 := inv_mul_cancel _
    exact congrArg (fun z : ℤˣ => (z : ℤ)) hunit
  have hterm (σ : Equiv.Perm (Fin n)) :
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (MonoidAlgebra.single σ ((σ.sign : ℤ) : ℚ))).comp F = F := by
    rw [coefficientRationalPermutationAction_single, LinearMap.smul_comp,
      coefficientPermutationRepresentation_comp_exteriorAntisymmetrization,
      smul_smul, map_intCast, ← Int.cast_mul, hsign, Int.cast_one, one_smul]
  rw [Equiv.Perm.eulerianElement_top, coefficientRationalPermutationAction_smul,
    LinearMap.smul_comp, map_sum]
  have hsum : (∑ σ : Equiv.Perm (Fin n),
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (MonoidAlgebra.single σ ((σ.sign : ℤ) : ℚ))).comp F =
    ∑ σ : Equiv.Perm (Fin n),
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (MonoidAlgebra.single σ ((σ.sign : ℤ) : ℚ))).comp F := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [hsum]
  change algebraMap ℚ k ((n.factorial : ℚ)⁻¹) •
    (∑ σ : Equiv.Perm (Fin n),
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (MonoidAlgebra.single σ ((σ.sign : ℤ) : ℚ))).comp F) = F
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul k, smul_smul]
  have hfac : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hscalar : algebraMap ℚ k ((n.factorial : ℚ)⁻¹) * (n.factorial : k) = 1 := by
    rw [← map_natCast (algebraMap ℚ k), ← map_mul, inv_mul_cancel₀ hfac, map_one]
  rw [hscalar, one_smul]

/-- Every other actual Eulerian weight vanishes on the original exterior image. -/
theorem coefficientEulerian_exteriorAntisymmetrization (n i : ℕ) :
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.eulerianElement n i)).comp
        (TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n)) =
          if i = n then TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n) else 0 := by
  by_cases hi : i = n
  · subst i
    rw [if_pos rfl]
    exact coefficientEulerian_top_exteriorAntisymmetrization k V M n
  · rw [if_neg hi]
    have hp := (Equiv.Perm.eulerianElement_projector_laws n).2 i n
    rw [if_neg hi] at hp
    let ρ := coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
    have hzero : (ρ (Equiv.Perm.eulerianElement n i)).comp
        (ρ (Equiv.Perm.eulerianElement n n)) = 0 := by
      change ρ (Equiv.Perm.eulerianElement n i) * ρ (Equiv.Perm.eulerianElement n n) = _
      rw [← map_mul, hp, map_zero]
    rw [← coefficientEulerian_top_exteriorAntisymmetrization k V M n,
      ← LinearMap.comp_assoc, hzero, LinearMap.zero_comp]

/-- The full actual rational convolution acts on exterior words by its homogeneous top eigenvalue. -/
theorem coefficientConvolution_exteriorAntisymmetrization (n : ℕ) (a : ℚ) :
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.eulerianLambda n a)).comp
        (TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n)) =
          algebraMap ℚ k (a ^ n) • TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n) := by
  classical
  let n₀ : Fin (n + 1) := Fin.last n
  rw [Equiv.Perm.eulerianLambda_eq_sum, map_sum]
  let F := TensorProduct.map (LinearMap.id : M →ₗ[k] M) (exteriorAntisymmetrization k V n)
  have hsum : (∑ j : Fin (n + 1),
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (a ^ j.val • Equiv.Perm.eulerianElement n j.val)).comp F =
    ∑ j : Fin (n + 1),
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (a ^ j.val • Equiv.Perm.eulerianElement n j.val)).comp F := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [hsum]
  dsimp only [F]
  simp only [coefficientRationalPermutationAction_smul, LinearMap.smul_comp,
    coefficientEulerian_exteriorAntisymmetrization]
  rw [Finset.sum_eq_single n₀]
  · simp [n₀]
  · intro j _ hj
    have hne : j.val ≠ n := fun he => hj (Fin.ext he)
    simp only [if_neg hne, smul_zero]
  · simp

end TensorPower
