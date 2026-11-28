/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianProjectors
public import MathlibExt.Combinatorics.Perm.EulerianShuffleMultiplication
public import MathlibExt.Algebra.Polynomial.NatInterpolation

/-!
# Rational Eulerian convolution and block actions

The family `Λ_n(a) = ∑_(i=0)^n a^i ε_(n,i)` in `ℚ[S_n]` satisfies `Λ_n(a)Λ_n(b)=Λ_n(ab)`. For
`a≠0`, its inverse is `Λ_n(a⁻¹)`. On the supported Eulerian element `ε_(n,i)`, multiplication
by `Λ_n(a)` has eigenvalue `a^i`.

Embedding the two block permutation groups gives `Λ_(p+q)(a) Sh_(p,q) = Sh_(p,q) (Λ_p(a)^L
Λ_q(a)^R)`, where `Sh_(p,q)` is the sum of shuffle permutations weighted by their signs.

For positive integer `m`, the parameter-signed lambda element is `(-1)^(m-1)` times the
convolution value. The rational family is defined by its polynomial coefficients.

Reference: Loday, *Cyclic Homology*, Section 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For `a,b : ℚ`, `Λ_n(a) * Λ_n(b) = Λ_n(a*b)`. -/
theorem eulerianLambda_mul (n : ℕ) (a b : ℚ) :
    eulerianLambda n a * eulerianLambda n b = eulerianLambda n (a * b) := by
  classical
  rw [eulerianLambda_eq_sum, eulerianLambda_eq_sum, eulerianLambda_eq_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    eulerianElement_mul_fin]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, ← mul_pow]
  · intro j hj hji
    rw [if_neg (Ne.symm hji), smul_zero]
  · simp

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For `i : ℕ` with `i≤n` and `a : ℚ`, `Λ_n(a) * ε_(n,i) = a^i • ε_(n,i)`. -/
theorem eulerianLambda_mul_eulerianElement (n i : ℕ) (hi : i ≤ n) (a : ℚ) :
    eulerianLambda n a * eulerianElement n i = a ^ i • eulerianElement n i := by
  classical
  let j₀ : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  rw [eulerianLambda_eq_sum, Finset.sum_mul]
  simp only [smul_mul_assoc]
  simp_rw [(eulerianElement_projector_laws n).2]
  rw [Finset.sum_eq_single j₀]
  · simp [j₀]
  · intro j hj hne
    have hji : j.val ≠ i := fun h => hne (Fin.ext h)
    simp [hji]
  · simp

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For `a : ℚ` with `a≠0`, `eulerianLambdaUnit n a ha` is the unit of `ℚ[S_n]` whose
value is `Λ_n(a)` and inverse value is `Λ_n(a⁻¹)`. -/
def eulerianLambdaUnit (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (MonoidAlgebra ℚ (Perm (Fin n)))ˣ where
  val := eulerianLambda n a
  inv := eulerianLambda n a⁻¹
  val_inv := by rw [eulerianLambda_mul, mul_inv_cancel₀ ha, eulerianLambda_one]
  inv_val := by rw [eulerianLambda_mul, inv_mul_cancel₀ ha, eulerianLambda_one]

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For `a : ℚ` with `a≠0`, `(eulerianLambdaUnit n a ha).val = Λ_n(a)`. -/
theorem eulerianLambdaUnit_val (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (eulerianLambdaUnit n a ha).val = eulerianLambda n a := rfl

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For `a : ℚ` with `a≠0`, `(eulerianLambdaUnit n a ha).inv = Λ_n(a⁻¹)`. -/
theorem eulerianLambdaUnit_inv (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (eulerianLambdaUnit n a ha).inv = eulerianLambda n a⁻¹ := rfl

/-- For `p,q : ℕ`, `eulerianBlockLeftAction p q : ℚ[S_p] →ₐ[ℚ] ℚ[S_(p+q)]` sends `[α]` to
`[blockPermutation p q α 1]`, acting in the left block and fixing the right block. -/
def eulerianBlockLeftAction (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin p)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockLeftHom p q)

/-- For `p,q : ℕ`, `eulerianBlockRightAction p q : ℚ[S_q] →ₐ[ℚ] ℚ[S_(p+q)]` sends `[β]` to
`[blockPermutation p q 1 β]`, fixing the left block and acting in the right block. -/
def eulerianBlockRightAction (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin q)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockRightHom p q)

/-- For `p,q : ℕ` and `a : ℚ`, `splitEulerianLambda p q a = B_L(Λ_p(a)) * B_R(Λ_q(a))` in
`ℚ[S_(p+q)]`, where `B_L,B_R` are the left and right block group-ring inclusions. -/
theorem splitEulerianLambda_eq_blockActions (p q : ℕ) (a : ℚ) :
    splitEulerianLambda p q a = eulerianBlockLeftAction p q (eulerianLambda p a) *
      eulerianBlockRightAction p q (eulerianLambda q a) := rfl

/-- For `p,q : ℕ` and `a : ℚ`, let `B_L,B_R` be the block group-ring inclusions and `ε_(r,i)` the
Eulerian coefficient elements. Then `splitEulerianLambda p q a = ∑ i : Fin(p+1), ∑ j :
Fin(q+1), a^(i.val+j.val) • (B_L ε_(p,i.val) * B_R ε_(q,j.val))`. -/
theorem splitEulerianLambda_eq_eulerian_sum (p q : ℕ) (a : ℚ) :
    splitEulerianLambda p q a =
      ∑ z : Fin (p + 1) × Fin (q + 1), a ^ (z.1.val + z.2.val) •
        (eulerianBlockLeftAction p q (eulerianElement p z.1.val) *
          eulerianBlockRightAction p q (eulerianElement q z.2.val)) := by
  classical
  rw [splitEulerianLambda_eq_blockActions, eulerianLambda_eq_sum, eulerianLambda_eq_sum,
    map_sum, map_sum]
  simp_rw [map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← pow_add]
  rw [Fintype.sum_prod_type]

/-- For `p,q : ℕ` and `a : ℚ`, put `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]`. Then
`Λ_(p+q)(a) * Sh_(p,q) = Sh_(p,q) * splitEulerianLambda p q a` in `ℚ[S_(p+q)]`. -/
theorem eulerianLambda_mul_signedShuffle_rat (p q : ℕ) (a : ℚ) :
    eulerianLambda (p + q) a * signedShuffleElement p q =
      signedShuffleElement p q * splitEulerianLambda p q a := by
  classical
  let left (z : Fin (p + q + 1)) := eulerianElement (p + q) z.val * signedShuffleElement p q
  let right (z : Fin (p + 1) × Fin (q + 1)) := signedShuffleElement p q *
    (eulerianBlockLeftAction p q (eulerianElement p z.1.val) *
      eulerianBlockRightAction p q (eulerianElement q z.2.val))
  have hleft (t : ℚ) : eulerianLambda (p + q) t * signedShuffleElement p q =
      Polynomial.finiteWeightedPowerCombination Fin.val left t := by
    rw [eulerianLambda_eq_sum, Finset.sum_mul]
    simp only [Polynomial.finiteWeightedPowerCombination, left, smul_mul_assoc]
  have hright (t : ℚ) : signedShuffleElement p q * splitEulerianLambda p q t =
      Polynomial.finiteWeightedPowerCombination (fun z => z.1.val + z.2.val) right t := by
    rw [splitEulerianLambda_eq_eulerian_sum, Finset.mul_sum]
    simp only [Polynomial.finiteWeightedPowerCombination, right, mul_smul_comm]
  rw [hleft, hright]
  apply Polynomial.finiteWeightedPowerCombination_eq_of_nat
  intro m
  rw [← hleft, ← hright]
  exact eulerianLambda_mul_signedShuffle p q m

end Equiv.Perm
