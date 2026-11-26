/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConstantTermLinearRepresentation

/-! # Tests for constant terms of powers of Laurent polynomials -/

open AddMonoidAlgebra MetaMathlibExt

example {R : Type*} [Semiring R] {r : ℕ} (F : AddMonoidAlgebra R (Fin r → ℤ)) :
    laurentCartier 0 F = 0 := by
  simp [laurentCartier]

-- Halving the even exponent keeps its coefficient and discards the odd exponent.
example (e : Fin 1 → ℤ) :
    laurentCartier 2 (single (2 • e) (5 : ℤ) + single (fun _ => -3) 7) = single e 5 := by
  classical
  ext j
  have hodd : (fun _ : Fin 1 => (-3 : ℤ)) ≠ 2 • j := by
    intro h
    have h₀ := congrFun h 0
    change -3 = (2 : ℕ) • j 0 at h₀
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h₀
    omega
  simp only [coeff_laurentCartier (by decide : 2 ≠ 0), coeff_add, Finsupp.add_apply,
    coeff_single, Finsupp.single_apply, hodd, ite_false, add_zero,
    (smul_right_injective (Fin 1 → ℤ) (by decide : (2 : ℕ) ≠ 0)).eq_iff]

-- The coefficients 9 and 5 agree modulo 4. The offset k = 2 is outside the digit range.
example (e : Fin 1 → ℤ) (Q : AddMonoidAlgebra ℤ (Fin 1 → ℤ)) :
    (single e 3 ^ 4 * Q).coeff 0 ≡
      (single e 5 * laurentCartier 2 (single e 3 ^ 2 * Q)).coeff 0 [ZMOD 4] := by
  have h (j : Fin 1 → ℤ) : (single (2 • e) (9 : ℤ)).coeff j ≡
      (single (2 • e) 5).coeff j [ZMOD 4] := by
    classical
    simp only [coeff_single, Finsupp.single_apply]
    split <;> decide
  simpa using constantTerm_pow_mul_modEq_tilde (p := 2) (a := 2) (ℓ := 1)
    (by decide) (by decide) (single e 3) (single e 5) (by simpa using h) Q 1 2

-- For P̃ = 8x and k = 4, the Cartier step reads the coefficient of x⁻⁷ in Q.
example (Q : AddMonoidAlgebra ℤ (Fin 1 → ℤ)) :
    (single (fun _ => 1) 8 ^ 7 * Q).coeff 0 ≡ 8 ^ 5 * Q.coeff (fun _ => -7) [ZMOD 9] := by
  let e : Fin 1 → ℤ := fun _ => 1
  have h (j : Fin 1 → ℤ) : (single (3 • e) (512 : ℤ)).coeff j ≡
      (single (3 • e) 8).coeff j [ZMOD 9] := by
    classical
    simp only [coeff_single, Finsupp.single_apply]
    split <;> decide
  have step := constantTerm_tilde_pow_mul_modEq_laurentCartier (p := 3) (a := 2)
    (by decide) (single e 8) (by simpa using h) Q 1 4
  simpa [coeff_laurentCartier (by decide : 3 ≠ 0), e, Pi.mul_def, Pi.neg_def, Pi.add_def,
    ← mul_assoc] using step

-- For P = xᵉ + x⁻ᵉ and P̃ = P + 2, the witness n = 2 transfers under dilation by 2.
example (e : Fin 1 → ℤ) (he : e ≠ 0) :
    (2 : ℤ) ∣ ((single e (1 : ℤ) + single (-e) 1 + single 0 2) ^ 2).coeff 0 := by
  let P : AddMonoidAlgebra ℤ (Fin 1 → ℤ) := single e 1 + single (-e) 1
  let Pt := P + single 0 2
  have hsq : P ^ 2 = mapDomain (fun j => (2 : ℕ) • j) Pt := by
    simp only [P, Pt, pow_two, add_mul, mul_add, single_mul_single, one_mul, add_neg_cancel,
      neg_add_cancel, mapDomain_add, mapDomain_single, two_nsmul, add_zero]
    rw [show (2 : ℤ) = 1 + 1 by decide, single_add]
    ac_rfl
  have he₂ : 2 * e ≠ 0 := by simpa using smul_ne_zero (by decide : (2 : ℕ) ≠ 0) he
  have hct : (P ^ 2).coeff 0 = 2 := by
    classical
    simp [P, pow_two, mul_add, add_mul, ← two_nsmul, he₂]
  apply (exists_constantTerm_pow_dvd_iff_tilde (p := 2) (a := 2) (ℓ := 1)
    (by decide) (by decide) P Pt (fun j => by simp [hsq])).2 2
  simp [hct]

-- With P = 3x^2 + 5, p = 2, m = 1 and i = 0, the Cartier operator keeps 3x + 5:
-- the sum over the box [-1, 1] reads the coefficients at exponents 2 and 0.
example :
    laurentCartier 2 ((single (fun _ : Fin 1 => (2 : ℤ)) (3 : ℤ) + single 0 5) ^ 1 *
      single 0 1) =
      single (fun _ : Fin 1 => (1 : ℤ)) 3 + single 0 5 := by
  have hm : laurentDeg (single (fun _ : Fin 1 => (2 : ℤ)) (3 : ℤ) + single 0 5) ≤
      1 + 1 := by
    rw [laurentDeg_le_iff]
    intro j hj t
    have hsub : (single (fun _ : Fin 1 => (2 : ℤ)) (3 : ℤ) + single 0 5).coeff.support ⊆
        {(fun _ : Fin 1 => (2 : ℤ)), 0} := by
      have h1 : (single (fun _ : Fin 1 => (2 : ℤ)) (3 : ℤ) + single 0 5).coeff.support ⊆
          (single (fun _ : Fin 1 => (2 : ℤ)) (3 : ℤ)).coeff.support ∪
            (single (0 : Fin 1 → ℤ) (5 : ℤ)).coeff.support := by
        rw [coeff_add]
        exact Finsupp.support_add
      have h2 : (single (fun _ : Fin 1 => (2 : ℤ)) (3 : ℤ)).coeff.support ⊆
          {(fun _ : Fin 1 => (2 : ℤ))} := by
        simp [coeff_single]
      have h3 : (single (0 : Fin 1 → ℤ) (5 : ℤ)).coeff.support ⊆ {0} := by
        simp [coeff_single]
      exact h1.trans (Finset.union_subset (h2.trans (by simp)) (h3.trans (by simp)))
    have hj2 := hsub hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj2
    rcases hj2 with rfl | rfl <;> simp
  have hi : (0 : Fin 1 → ℤ) ∈
      Fintype.piFinset fun _ : Fin 1 => Finset.Icc (-(1 : ℤ)) 1 := by simp
  have h := laurentCartier_pow_mul_single_eq_sum (r := 1) (p := 2) Nat.prime_two
    (single (fun _ : Fin 1 => (2 : ℤ)) (3 : ℤ) + single 0 5) 1 hm 1 (by decide)
    (0 : Fin 1 → ℤ) hi
  have hT : Fintype.piFinset (fun _ : Fin 1 => Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)) =
      {(fun _ : Fin 1 => (-1 : ℤ)), (fun _ : Fin 1 => (0 : ℤ)),
        (fun _ : Fin 1 => (1 : ℤ))} := by
    decide
  rw [hT] at h
  rw [h]
  clear h hm hi hT
  ext j
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, pow_one]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  generalize ha : j 0 = a
  have hj : j = fun _ => a := by funext t; rw [← ha]; congr 1; exact Subsingleton.elim t 0
  subst hj
  by_cases h1 : a = -1 <;> by_cases h0 : a = 0 <;> by_cases h1' : a = 1
  all_goals simp [h1, h0, h1', funext_iff, nsmul_eq_mul]
  omega

-- Doubling sends -1 to the boundary -2 on the first step. That entry eventually vanishes.
example :
    let T := Fintype.piFinset fun _ : Fin 1 => Finset.Icc (-2 : ℤ) 2
    let A := Matrix.of fun i j : ↥T => if i.val = (2 : ℕ) • j.val then (1 : ZMod 2) else 0
    let i : ↥T := ⟨fun _ => -2, by decide⟩
    let j : ↥T := ⟨fun _ => -1, by decide⟩
    A i j = 1 ∧ ∃ s : ℕ, ∀ n ≥ s, (A ^ n) i j = 0 := by
  intro T A i j
  refine ⟨by decide +revert, ?_⟩
  obtain ⟨s, hs⟩ := exists_gammaZero_pow_eq_single Nat.prime_two 1 2
  refine ⟨s, fun n hn => ?_⟩
  exact (congrArg (fun M : Matrix T T (ZMod 2) => M i j) (hs n hn)).trans (by decide +revert)

-- Modulo 8, the initial dilation sends -1 to -2. That entry eventually vanishes,
-- and the origin entry of each stabilized power is 1.
example :
    let T := Fintype.piFinset fun _ : Fin 1 => Finset.Icc (-2 : ℤ) 2
    let A := Matrix.of fun i j : ↥T => if i.val = (2 : ℕ) • j.val then (1 : ZMod 8) else 0
    let i : ↥T := ⟨fun _ => -2, by decide⟩
    let j : ↥T := ⟨fun _ => -1, by decide⟩
    let z : ↥T := ⟨0, by decide⟩
    A i j = 1 ∧ ∃ s : ℕ, ∀ n ≥ s, (A ^ n) i j = 0 ∧ (A ^ n) z z = 1 := by
  intro T A i j z
  refine ⟨by decide +revert, ?_⟩
  obtain ⟨s, hs⟩ := exists_gammaZero_pow_eq_single_zmod Nat.prime_two 3 (by decide) 1 2
  refine ⟨s, fun n hn => ⟨?_, ?_⟩⟩
  · exact (congrArg (fun M : Matrix T T (ZMod 8) => M i j) (hs n hn)).trans (by decide +revert)
  · exact (congrArg (fun M : Matrix T T (ZMod 8) => M z z) (hs n hn)).trans (by decide +revert)

-- A zero-width box has only the origin: the stabilized matrix is the identity.
example :
    let T := Fintype.piFinset fun _ : Fin 1 => Finset.Icc (-(0 : ℤ)) 0
    let A := Matrix.of fun i j : ↥T => if i.val = (3 : ℕ) • j.val then (1 : ZMod 9) else 0
    ∃ s : ℕ, ∀ n ≥ s, A ^ n = 1 := by
  intro T A
  obtain ⟨s, hs⟩ := exists_gammaZero_pow_eq_single_zmod Nat.prime_three 2 (by decide) 1 0
  exact ⟨s, fun n hn => (hs n hn).trans (by decide +revert)⟩
