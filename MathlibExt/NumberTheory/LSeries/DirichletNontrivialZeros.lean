/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The nontrivial zeros of a Dirichlet `L`-function

The nontrivial zeros of `L(s, χ)` are its zeros in the open critical strip `0 < Re s < 1`.

The strip is open so that the definition is right for every `χ`. For imprimitive `χ` induced by
the primitive character `χ*`, `L(s, χ) = L(s, χ*) ∏_{p ∣ q} (1 - χ*(p) p^{-s})`, and the Euler
factors vanish at infinitely many points of the line `Re s = 0`; these zeros are trivial, and the
open strip excludes them. The Euler factors do not vanish on `0 < Re s < 1`, so `χ` and `χ*` have
the same nontrivial zeros (`DirichletCharacter.nontrivialZeros_primitiveCharacter`). For primitive
`χ` nothing is lost: `L(s, χ)` has no zeros on `Re s = 1`, and by the functional equation none on
`Re s = 0` except the trivial zero `s = 0` of an even `χ ≠ 1`.

The set is a `Set ℂ`: zeros are counted without multiplicity. The zero-counting function
`N(T, χ)` counts them with multiplicity.

## Main definitions

* `DirichletCharacter.nontrivialZeros χ`: the nontrivial zeros of `L(s, χ)`.
* `DirichletCharacter.zeroCount χ T`: the number `N(T, χ)` of nontrivial zeros with `|Im s| < T`,
  counted with multiplicity.

## Main statements

* `DirichletCharacter.nontrivialZeros_changeLevel`,
  `DirichletCharacter.nontrivialZeros_primitiveCharacter`: changing the level of `χ` does not
  change its nontrivial zeros.
* `DirichletCharacter.zeroCount_mono`: `N(T, χ)` is monotone in `T` when the zeros are locally
  finite.
-/

@[expose] public section

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The **nontrivial zeros** of the Dirichlet `L`-function `L(s, χ)`: the zeros of
`DirichletCharacter.LFunction χ` in the open critical strip `0 < Re s < 1`. The strip is open, so
the trivial zero `s = 0` of an even character and the zeros on `Re s = 0` of the Euler factors of
an imprimitive character are excluded; `χ` and its primitive character have the same nontrivial
zeros (`DirichletCharacter.nontrivialZeros_primitiveCharacter`). -/
def nontrivialZeros : Set ℂ :=
  {s | LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1}

variable {χ}

/-- Membership in the nontrivial zeros, unfolded. -/
theorem mem_nontrivialZeros {s : ℂ} :
    s ∈ χ.nontrivialZeros ↔ LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1 :=
  Iff.rfl

/-- A nontrivial zero is a zero of `L(s, χ)`. -/
theorem LFunction_eq_zero_of_mem_nontrivialZeros {s : ℂ} (hs : s ∈ χ.nontrivialZeros) :
    LFunction χ s = 0 :=
  hs.1

/-- Nontrivial zeros lie in the half-plane `Re s > 0`. -/
theorem re_pos_of_mem_nontrivialZeros {s : ℂ} (hs : s ∈ χ.nontrivialZeros) : 0 < s.re :=
  hs.2.1

/-- Nontrivial zeros lie in the half-plane `Re s < 1`. -/
theorem re_lt_one_of_mem_nontrivialZeros {s : ℂ} (hs : s ∈ χ.nontrivialZeros) : s.re < 1 :=
  hs.2.2

/-- `s = 0` is not a nontrivial zero. -/
theorem ne_zero_of_mem_nontrivialZeros {s : ℂ} (hs : s ∈ χ.nontrivialZeros) : s ≠ 0 := by
  rintro rfl
  exact (re_pos_of_mem_nontrivialZeros hs).ne' rfl

/-- A zero of `L(s, χ)` in the open critical strip is a nontrivial zero. -/
theorem mem_nontrivialZeros_of_LFunction_eq_zero {s : ℂ} (hs : LFunction χ s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) : s ∈ χ.nontrivialZeros :=
  ⟨hs, h0, h1⟩

/-- The Euler factor `1 - χ(p) p^{-s}` does not vanish for `Re s > 0`. -/
private lemma one_sub_mul_cpow_neg_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) : 1 - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hnorm : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    have h1 : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
    calc ‖ψ p‖ * (p : ℝ) ^ (-s.re) ≤ 1 * (p : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (ψ.norm_le_one _) (by positivity)
      _ < 1 := by rwa [one_mul]
  rw [← h, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- **Changing the level does not change the nontrivial zeros.** If `M ∣ N` and `χ` is a
Dirichlet character mod `M`, then `χ` regarded mod `N` has the same nontrivial zeros: the extra
Euler factors `1 - χ(p) p^{-s}` do not vanish for `Re s > 0`. -/
theorem nontrivialZeros_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (ψ : DirichletCharacter ℂ M) : (changeLevel hMN ψ).nontrivialZeros = ψ.nontrivialZeros := by
  ext s
  simp only [mem_nontrivialZeros]
  refine and_congr_left fun hs => ?_
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs.2
  rw [LFunction_changeLevel hMN ψ (.inr hs1), mul_eq_zero, or_iff_left]
  rw [Finset.prod_eq_zero_iff, not_exists]
  exact fun p ⟨hp, h⟩ => one_sub_mul_cpow_neg_ne_zero ψ (Nat.prime_of_mem_primeFactors hp) hs.1 h

/-- **A character and its primitive character have the same nontrivial zeros.** -/
theorem nontrivialZeros_primitiveCharacter (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] :
    χ.primitiveCharacter.nontrivialZeros = χ.nontrivialZeros := by
  conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
  exact (nontrivialZeros_changeLevel _ _).symm

/-! ### Counting the nontrivial zeros -/

variable (χ) in
/-- **`N(T, χ)`**: the number of nontrivial zeros `ρ` of `L(s, χ)` with `|Im ρ| < T`, counted
with multiplicity (`analyticOrderNatAt`). If there were infinitely many such zeros, the `finsum`
would take the junk value `0`; for primitive `χ` there are finitely many
(`DirichletCharacter.finite_setOf_mem_nontrivialZeros_abs_im_lt`). -/
noncomputable def zeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ | ρ ∈ χ.nontrivialZeros ∧ |ρ.im| < T}, analyticOrderNatAt (LFunction χ) ρ

/-- `N(T, χ) = 0` for `T ≤ 0`. -/
theorem zeroCount_of_nonpos {T : ℝ} (hT : T ≤ 0) : χ.zeroCount T = 0 := by
  have h : {ρ | ρ ∈ χ.nontrivialZeros ∧ |ρ.im| < T} = ∅ :=
    Set.eq_empty_of_forall_notMem fun ρ hρ => (abs_nonneg ρ.im).not_gt (hρ.2.trans_le hT)
  rw [zeroCount, h, finsum_mem_empty]

/-- `N(T, χ)` is monotone in `T`, as long as the zeros up to the larger height are finite. -/
theorem zeroCount_mono {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hfin : {ρ | ρ ∈ χ.nontrivialZeros ∧ |ρ.im| < T₂}.Finite) :
    χ.zeroCount T₁ ≤ χ.zeroCount T₂ := by
  have hsub : {ρ | ρ ∈ χ.nontrivialZeros ∧ |ρ.im| < T₁} ⊆
      {ρ | ρ ∈ χ.nontrivialZeros ∧ |ρ.im| < T₂} := fun _ hρ => ⟨hρ.1, hρ.2.trans_le hT⟩
  rw [zeroCount, zeroCount, finsum_mem_eq_finite_toFinset_sum _ (hfin.subset hsub),
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Finset.sum_le_sum_of_subset (Set.Finite.toFinset_subset_toFinset.mpr hsub)

end DirichletCharacter
