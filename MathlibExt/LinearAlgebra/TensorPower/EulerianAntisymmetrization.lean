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
# Eulerian operators on antisymmetric tensors

Let k be a commutative ℚ-algebra and M,V k-modules. On M ⊗ V⊗n, let F = id_M ⊗ Aₙ be the
exterior antisymmetrization. The rational Eulerian projector eₙ⁽ⁿ⁾ fixes the image of F, every
projector eₙ⁽ⁱ⁾ with i ≠ n kills it, and the convolution family Λₙ(a) acts there by aⁿ for a ∈
ℚ.

The Eulerian idempotents and their signed top term are discussed in J.-L. Loday, Cyclic
Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (V : Type v) [AddCommGroup V] [Module k V]
  (M : Type w) [AddCommGroup M] [Module k M]

/-- The action of a rational permutation monomial.

For a commutative ℚ-algebra k, k-modules M,V, σ ∈ Sₙ and c ∈ ℚ, the coefficient tensor
action of c[σ] is algebraMap(c) · ρₙ(σ). The operator ρₙ(σ) fixes M and sends a tensor word
a to a ∘ σ⁻¹. -/
theorem coefficientRationalPermutationAction_single (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (c : ℚ) :
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (MonoidAlgebra.single σ c) =
      algebraMap ℚ k c • coefficientPermutationRepresentation (k := k) (M := M) (V := V) n σ := by
  change coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
    ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))
      (MonoidAlgebra.single σ c)) = _
  rw [MonoidAlgebra.mapRingHom_single, coefficientPermutationGroupAlgebraAction_single]

/-- The top Eulerian projector fixes antisymmetrized tensors.

For a commutative ℚ-algebra k and k-modules M,V, let F = id_M ⊗ Aₙ : M ⊗ ⋀ⁿV → M ⊗ V⊗n. Then
the action of eₙ⁽ⁿ⁾ satisfies eₙ⁽ⁿ⁾ ∘ F = F. -/
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

/-- Eulerian weights of antisymmetrized tensors.

For a commutative ℚ-algebra k and k-modules M,V, the action of eₙ⁽ⁱ⁾ on F = id_M ⊗ Aₙ is F
when i = n and zero when i ≠ n. Thus the exterior image has Eulerian weight n. -/
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

/-- The convolution eigenvalue on antisymmetrized tensors.

For a commutative ℚ-algebra k, k-modules M,V and a ∈ ℚ, the action of Λₙ(a) = ∑ᵢaⁱeₙ⁽ⁱ⁾
satisfies Λₙ(a) ∘ (id_M ⊗ Aₙ) = algebraMap(aⁿ) · (id_M ⊗ Aₙ). -/
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
