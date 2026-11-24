/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/RingTheory/CyclicCohomology/ConnesOperator.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import MathlibExt.RingTheory.CyclicCochains
import Mathlib.Algebra.BigOperators.Intervals
import MathlibExt.Algebra.BigOperators.CyclicAlternatingSum
import MathlibExt.Data.Fin.CyclicCoordinates

/-!
# The cyclic operator, the bar coboundary and Connes' operator `B`

For an `R`-algebra `A` and an `R`-module `M`, this file constructs the operators on the
`M`-valued multilinear cochains `Cⁿ` of `A` from which Connes' cyclic bicomplex and the
`(b, B)` mixed complex are built:

* the cyclic operator `λ : Cⁿ → Cⁿ`, `(λφ)(a₀, …, aₙ) = (-1)ⁿ φ(aₙ, a₀, …, aₙ₋₁)`, whose fixed
  points are the cyclic cochains and which satisfies `λⁿ⁺¹ = 1`;
* the cyclic norm `N = 1 + λ + ⋯ + λⁿ`;
* the bar coboundary `b' : Cⁿ → Cⁿ⁺¹`, the alternating sum of all Hochschild cofaces but the
  last one;
* for unital `A`, the contraction `s : Cⁿ⁺¹ → Cⁿ`, `(sφ)(a₀, …, aₙ) = φ(1, a₀, …, aₙ)`, of the
  bar complex;
* Connes' operator `B = N s (1 - λ) : Cⁿ⁺¹ → Cⁿ`.

The identities `(1 - λ) b = b' (1 - λ)` and `b N = N b'` are the commutation relations of the
cyclic bicomplex, whose columns alternate between `b` and `-b'` and whose rows alternate between
`1 - λ` and `N`. Together with `b' s + s b' = 1` they give `B ∘ B = 0` and `b B + B b = 0`, so
that `(C*, b, B)` is a mixed complex. These are the cochain (transposed) forms of the chain-level
identities in Loday's book; for example `B` is the transpose of `(1 - t) s N`. The operator `B`
vanishes on cyclic cochains and takes values in them.

The bicomplex identities hold for nonunital and nonassociative `A`; among the results here only
`b' ∘ b' = 0` uses associativity, and the identities for `B` only use that `1` is a left unit.

## Main definitions

* `TauCeti.cyclicOperator`: the cyclic operator `λ`.
* `TauCeti.cyclicNorm`: the cyclic norm `N`.
* `TauCeti.barCoboundary`: the bar coboundary `b'`.
* `TauCeti.barContraction`: the contraction `s` of the bar complex of a unital algebra.
* `TauCeti.connesB`: Connes' operator `B`.

## Main results

* `TauCeti.cyclicOperator_pow_eq_one`: `λⁿ⁺¹ = 1`.
* `TauCeti.mem_cyclicCochains_iff_cyclicOperator_apply_eq_self`: the cyclic cochains are the
  fixed points of `λ`.
* `TauCeti.barCoboundary_barCoboundary`: `b' ∘ b' = 0`.
* `TauCeti.one_sub_cyclicOperator_comp_hochschildCoboundary`: `(1 - λ) b = b' (1 - λ)`.
* `TauCeti.cyclicNorm_hochschildCoface_of_mem_cyclicCochains`: `N (δᵢ φ) = (-1)ⁱ b φ` on cyclic
  cochains.
* `TauCeti.hochschildCoboundary_comp_cyclicNorm`: `b N = N b'`.
* `TauCeti.barCoboundary_comp_barContraction_add_barContraction_comp_barCoboundary`:
  `b' s + s b' = 1`.
* `TauCeti.connesB_comp_connesB`: `B ∘ B = 0`.
* `TauCeti.hochschildCoboundary_comp_connesB_add_connesB_comp_hochschildCoboundary`:
  `b B + B b = 0`.
* `TauCeti.connesB_hochschildCoboundary_zero`: `B b = 0` on degree-zero cochains.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.1, 2.1.
-/

public section

open Function

namespace TauCeti

/-! ### The cyclic operator and the cyclic norm -/

section CyclicOperator

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M] [SMulCommClass R R M]

/-- The cyclic operator `λ` on `n`-cochains, `(λφ)(a₀, …, aₙ) = (-1)ⁿ φ(aₙ, a₀, …, aₙ₋₁)`. -/
def cyclicOperator (n : ℕ) : Module.End R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
    M) where
  toFun φ := (-1 : ℤ) ^ n • φ.domDomCongr (finRotate (n + 1)).symm
  map_add' φ ψ := by
    ext
    simp
  map_smul' c φ := by
    ext
    simp [smul_comm c]

variable {R A M} {n : ℕ}

/-- The cyclic operator rotates the arguments cyclically and multiplies by `(-1)ⁿ`. -/
@[simp]
theorem cyclicOperator_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 1) → A) :
    cyclicOperator R A M n φ a = (-1 : ℤ) ^ n • φ (a ∘ (finRotate (n + 1)).symm) :=
  (rfl)

/-- The powers of the cyclic operator: `(λᵏφ)(a) = (-1)ⁿᵏ φ(a ∘ t⁻ᵏ)` for the cyclic rotation
`t` of the arguments. -/
theorem cyclicOperator_pow_apply (k : ℕ) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦
    A) M)
    (a : Fin (n + 1) → A) :
    (cyclicOperator R A M n ^ k) φ a =
      (-1 : ℤ) ^ (n * k) • φ (a ∘ (finRotate (n + 1) ^ k).symm) := by
  induction k generalizing a with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, mul_zero, one_smul, Equiv.Perm.one_def,
      Equiv.refl_symm, Equiv.coe_refl, comp_id]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, cyclicOperator_apply, ih, smul_smul, ← pow_add,
      mul_add_one, add_comm (n * k), pow_succ, Equiv.Perm.mul_def, Equiv.symm_trans,
      Equiv.coe_trans, comp_assoc]

/-- The cyclic operator on `n`-cochains has order dividing `n + 1`. -/
theorem cyclicOperator_pow_eq_one (n : ℕ) : cyclicOperator R A M n ^ (n + 1) = 1 := by
  have hrot : finRotate (n + 1) ^ (n + 1) = 1 :=
    Equiv.ext fun c ↦ Fin.ext <| by
      rw [Fin.coe_finRotate_pow, Nat.add_mod_right, Nat.mod_eq_of_lt c.isLt, Equiv.Perm.one_apply]
  ext φ a
  rw [cyclicOperator_pow_apply, hrot, (Nat.even_mul_succ_self n).neg_one_pow, one_smul,
    Equiv.Perm.one_def, Equiv.refl_symm, Equiv.coe_refl, comp_id, Module.End.one_apply]

/-- The cyclic cochains are the fixed points of the cyclic operator. -/
theorem mem_cyclicCochains_iff_cyclicOperator_apply_eq_self
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M} :
    φ ∈ cyclicCochains R A M n ↔ cyclicOperator R A M n φ = φ := by
  rw [mem_cyclicCochains_iff, MultilinearMap.ext_iff]
  refine forall_congr' fun a ↦ ?_
  rw [cyclicOperator_apply]
  constructor <;> intro h
  · rw [h, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  · rw [← h, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

variable (R A M) in
/-- The cyclic norm `N = 1 + λ + ⋯ + λⁿ` on `n`-cochains. -/
def cyclicNorm (n : ℕ) : Module.End R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :=
  ∑ k ∈ Finset.range (n + 1), cyclicOperator R A M n ^ k

variable (R A M n) in
/-- The cyclic norm is the sum of the powers `λᵏ`, `k ≤ n`, of the cyclic operator. -/
theorem cyclicNorm_def :
    cyclicNorm R A M n = ∑ k ∈ Finset.range (n + 1), cyclicOperator R A M n ^ k :=
  (rfl)

/-- The cyclic norm evaluates as the signed sum of `φ` over the cyclic rotations of the
arguments. -/
theorem cyclicNorm_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 1) → A) :
    cyclicNorm R A M n φ a =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n * k) • φ (a ∘ (finRotate (n + 1) ^ k).symm) := by
  simp [cyclicNorm_def, LinearMap.sum_apply, cyclicOperator_pow_apply]

/-- The cyclic norm absorbs the cyclic operator on the left: `λ N = N`. -/
@[simp]
theorem cyclicOperator_mul_cyclicNorm :
    cyclicOperator R A M n * cyclicNorm R A M n = cyclicNorm R A M n := by
  have h := (Finset.sum_range_succ' (fun k ↦ cyclicOperator R A M n ^ k) (n + 1)).symm.trans
    (Finset.sum_range_succ (fun k ↦ cyclicOperator R A M n ^ k) (n + 1))
  rw [cyclicOperator_pow_eq_one, pow_zero, add_left_inj] at h
  rw [cyclicNorm_def, Finset.mul_sum]
  simp_rw [← pow_succ']
  exact h

/-- The cyclic norm absorbs the cyclic operator on the right: `N λ = N`. -/
@[simp]
theorem cyclicNorm_mul_cyclicOperator :
    cyclicNorm R A M n * cyclicOperator R A M n = cyclicNorm R A M n := by
  refine (Commute.sum_left _ _ _ fun k _ ↦ (Commute.self_pow _ k).symm).eq.trans ?_
  exact cyclicOperator_mul_cyclicNorm

/-- The cyclic norm absorbs every power of the cyclic operator on the left. -/
@[simp]
theorem cyclicOperator_pow_mul_cyclicNorm (k : ℕ) :
    cyclicOperator R A M n ^ k * cyclicNorm R A M n = cyclicNorm R A M n := by
  induction k with
  | zero => rw [pow_zero, one_mul]
  | succ k ih => rw [pow_succ, mul_assoc, cyclicOperator_mul_cyclicNorm, ih]

/-- The cyclic norm absorbs every power of the cyclic operator on the right. -/
@[simp]
theorem cyclicNorm_mul_cyclicOperator_pow (k : ℕ) :
    cyclicNorm R A M n * cyclicOperator R A M n ^ k = cyclicNorm R A M n := by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k ih => rw [pow_succ', ← mul_assoc, cyclicNorm_mul_cyclicOperator, ih]

/-- The cyclic norm of any cochain is a cyclic cochain. -/
theorem cyclicNorm_mem_cyclicCochains (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
    M) :
    cyclicNorm R A M n φ ∈ cyclicCochains R A M n := by
  rw [mem_cyclicCochains_iff_cyclicOperator_apply_eq_self, ← Module.End.mul_apply,
    cyclicOperator_mul_cyclicNorm]

/-- On a cyclic cochain, the cyclic norm is multiplication by the number of arguments. -/
theorem cyclicNorm_apply_of_mem_cyclicCochains
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ cyclicCochains R A M n) :
    cyclicNorm R A M n φ = (n + 1 : R) • φ := by
  have hfix := mem_cyclicCochains_iff_cyclicOperator_apply_eq_self.1 hφ
  simp only [cyclicNorm_def, LinearMap.sum_apply, Module.End.pow_apply,
    Function.iterate_fixed hfix]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul R,
    Nat.cast_add, Nat.cast_one]

/-- The fixed-point submodule of the cyclic operator is the kernel of `1 - λ`. -/
theorem ker_one_sub_cyclicOperator :
    LinearMap.ker (1 - cyclicOperator R A M n) = cyclicCochains R A M n := by
  ext φ
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    mem_cyclicCochains_iff_cyclicOperator_apply_eq_self]
  exact eq_comm

end CyclicOperator

/-! ### Hochschild faces of tuples starting with a given entry -/

section Face

variable {A : Type*} {n : ℕ}

/-- The zeroth Hochschild face of `(1, a₀, …, aₙ)` is `(a₀, …, aₙ)`. -/
theorem hochschildFace_zero_cons_one [MulOneClass A] (a : Fin (n + 1) → A) :
    hochschildFace 0 (Fin.cons 1 a : Fin (n + 2) → A) = a := by
  rw [← Fin.castSucc_zero, hochschildFace_castSucc]
  funext k
  cases k using Fin.cases <;> simp [Fin.contractNth]

/-- A Hochschild face other than the last one of `(x, a₀, …, aₙ₊₁)` is `x` followed by the
previous face of `(a₀, …, aₙ₊₁)`. -/
theorem hochschildFace_succ_castSucc_cons [Mul A] (i : Fin (n + 1)) (x : A)
    (a : Fin (n + 2) → A) :
    hochschildFace i.succ.castSucc (Fin.cons x a : Fin (n + 3) → A) =
      Fin.cons x (hochschildFace i.castSucc a) := by
  rw [hochschildFace_castSucc, hochschildFace_castSucc]
  funext k
  cases k using Fin.cases <;> simp [Fin.contractNth]

end Face

/-! ### The cyclic operator and the Hochschild cofaces -/

section Coface

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- The cyclic operator turns the zeroth coface into the last one:
`λ (δ₀ φ) = (-1)ⁿ⁺¹ δₙ₊₁ φ`. -/
theorem cyclicOperator_hochschildCoface_zero (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n +
    1) ↦ A) M) :
    cyclicOperator R A M (n + 1) (hochschildCoface R A M 0 φ) =
      (-1 : ℤ) ^ (n + 1) • hochschildCoface R A M (Fin.last (n + 1)) φ := by
  ext a
  simp [hochschildFace_zero_comp_finRotate_symm]

/-- The cyclic operator moves the cofaces down: `λ (δᵢ₊₁ φ) = -δᵢ (λ φ)`. -/
theorem cyclicOperator_hochschildCoface_succ (i : Fin (n + 1))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicOperator R A M (n + 1) (hochschildCoface R A M i.succ φ) =
      -hochschildCoface R A M i.castSucc (cyclicOperator R A M n φ) := by
  ext a
  simp only [cyclicOperator_apply, hochschildCoface_apply, hochschildFace_succ_comp_finRotate_symm,
    _root_.neg_apply, pow_succ' (-1 : ℤ) n, neg_one_mul, neg_smul]

/-- The `k`-th power of the cyclic operator moves the `k`-th coface to the zeroth one:
`λᵏ (δₖ φ) = (-1)ᵏ δ₀ (λᵏ φ)`. -/
theorem cyclicOperator_pow_hochschildCoface (k : ℕ) (hk : k < n + 2)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    (cyclicOperator R A M (n + 1) ^ k) (hochschildCoface R A M ⟨k, hk⟩ φ) =
      (-1 : ℤ) ^ k • hochschildCoface R A M 0 ((cyclicOperator R A M n ^ k) φ) := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    have h := cyclicOperator_hochschildCoface_succ (R := R) (A := A) (M := M) (n := n)
      ⟨k, by omega⟩ φ
    rw [Fin.succ_mk, Fin.castSucc_mk] at h
    rw [pow_succ, Module.End.mul_apply, h, map_neg, ih (Nat.lt_of_succ_lt hk),
      ← Module.End.mul_apply _ (cyclicOperator R A M n), ← pow_succ, pow_succ (-1 : ℤ),
      mul_neg_one, neg_smul]

end Coface

/-! ### The bar coboundary and the cyclic bicomplex -/

section Bar

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The bar coboundary `b' : Cⁿ → Cⁿ⁺¹`, the alternating sum `∑_{i ≤ n} (-1)ⁱ δᵢ` of the
Hochschild cofaces other than the last one. -/
def barCoboundary (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R A M i.castSucc

variable {R A M} {n : ℕ}

/-- The bar coboundary evaluates as the alternating sum of `φ` on the contractions of adjacent
entries, `(b'φ)(a₀, …, aₙ₊₁) = ∑_{j ≤ n} (-1)ʲ φ(a₀, …, aⱼaⱼ₊₁, …, aₙ₊₁)`. -/
@[simp]
theorem barCoboundary_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 2) → A) :
    barCoboundary R A M n φ a =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • φ (Fin.contractNth j.castSucc (· * ·) a) := by
  simp [barCoboundary]

/-- The Hochschild coboundary of `φ` is the alternating sum of its cofaces. -/
private theorem hochschildCoboundary_eq_sum (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1)
    ↦ A) M) :
    hochschildCoboundary R A M n φ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R A M i φ := by
  ext a
  simp

/-- The Hochschild coboundary is the bar coboundary plus the signed last coface. -/
theorem hochschildCoboundary_eq_barCoboundary_add
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    hochschildCoboundary R A M n φ =
      barCoboundary R A M n φ +
        (-1 : ℤ) ^ (n + 1) • hochschildCoface R A M (Fin.last (n + 1)) φ := by
  ext a
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add]
  simp

/-- Conjugating the Hochschild coboundary by the cyclic operator gives the bar coboundary up to
the last coface: `λ (b φ) = b' (λ φ) + (-1)ⁿ⁺¹ δₙ₊₁ φ`. -/
theorem cyclicOperator_hochschildCoboundary (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1)
    ↦ A) M) :
    cyclicOperator R A M (n + 1) (hochschildCoboundary R A M n φ) =
      barCoboundary R A M n (cyclicOperator R A M n φ) +
        (-1 : ℤ) ^ (n + 1) • hochschildCoface R A M (Fin.last (n + 1)) φ := by
  rw [hochschildCoboundary_eq_sum, map_sum, Fin.sum_univ_succ, map_zsmul, Fin.val_zero, pow_zero,
    one_smul, cyclicOperator_hochschildCoface_zero]
  refine (add_comm _ _).trans ?_
  congr 1
  rw [barCoboundary, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, cyclicOperator_hochschildCoface_succ, LinearMap.smul_apply, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, smul_neg, neg_neg]

variable (R A M n) in
/-- The first commutation relation of the cyclic bicomplex: `(1 - λ) b = b' (1 - λ)`. -/
theorem one_sub_cyclicOperator_comp_hochschildCoboundary :
    (1 - cyclicOperator R A M (n + 1)) ∘ₗ hochschildCoboundary R A M n =
      barCoboundary R A M n ∘ₗ (1 - cyclicOperator R A M n) := by
  ext φ : 1
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.sub_apply,
    Module.End.one_apply, Module.End.one_apply, cyclicOperator_hochschildCoboundary,
    hochschildCoboundary_eq_barCoboundary_add, map_sub]
  abel

/-- `N (b' φ) = N (δ₀ (N φ))`: after the cyclic norm, every face of the bar coboundary becomes
the zeroth one. -/
private theorem cyclicNorm_barCoboundary (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦
    A) M) :
    cyclicNorm R A M (n + 1) (barCoboundary R A M n φ) =
      cyclicNorm R A M (n + 1) (hochschildCoface R A M 0 (cyclicNorm R A M n φ)) := by
  have hface (i : Fin (n + 1)) :
      (-1 : ℤ) ^ (i : ℕ) • cyclicNorm R A M (n + 1) (hochschildCoface R A M i.castSucc φ) =
        cyclicNorm R A M (n + 1)
          (hochschildCoface R A M 0 ((cyclicOperator R A M n ^ (i : ℕ)) φ)) := by
    rcases i with ⟨i, hi⟩
    conv_lhs => rw [← cyclicNorm_mul_cyclicOperator_pow i]
    rw [Module.End.mul_apply, Fin.castSucc_mk, cyclicOperator_pow_hochschildCoface, map_zsmul,
      smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  rw [barCoboundary, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, map_zsmul, hface]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ cyclicNorm R A M (n + 1)
    (hochschildCoface R A M 0 ((cyclicOperator R A M n ^ i) φ))), ← map_sum, ← map_sum]
  congr 2
  rw [cyclicNorm_def, LinearMap.sum_apply]

/-- On a cyclic `n`-cochain `φ`, the cyclic norm of the `i`-th Hochschild coface is `(-1)ⁱ` times
the Hochschild coboundary `b φ`. -/
theorem cyclicNorm_hochschildCoface_of_mem_cyclicCochains
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ cyclicCochains R A M n)
    (i : Fin (n + 2)) :
    cyclicNorm R A M (n + 1) (hochschildCoface R A M i φ) =
      (-1 : ℤ) ^ (i : ℕ) • hochschildCoboundary R A M n φ := by
  have hcyc : cyclicOperator R A M n φ = φ :=
    mem_cyclicCochains_iff_cyclicOperator_apply_eq_self.1 hφ
  have hface (j : Fin (n + 2)) :
      (-1 : ℤ) ^ (j : ℕ) • hochschildCoface R A M j φ =
        (cyclicOperator R A M (n + 1) ^ (n + 1 - j + 1)) (hochschildCoface R A M 0 φ) := by
    rcases j with ⟨j, hj⟩
    have hpow : cyclicOperator R A M (n + 1) ^ (n + 1 - j + 1) *
        cyclicOperator R A M (n + 1) ^ j = 1 := by
      rw [← pow_add, show n + 1 - j + 1 + j = n + 1 + 1 by omega, cyclicOperator_pow_eq_one]
    have hcyc_pow : (cyclicOperator R A M n ^ j) φ = φ := by
      rw [Module.End.pow_apply, Function.iterate_fixed hcyc]
    conv_lhs =>
      rw [← Module.End.one_apply (R := R) (hochschildCoface R A M ⟨j, hj⟩ φ),
        ← hpow]
    rw [Module.End.mul_apply, cyclicOperator_pow_hochschildCoface, hcyc_pow, map_zsmul,
      smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  have hsum : ∑ j ∈ Finset.range (n + 2), cyclicOperator R A M (n + 1) ^ (n + 1 - j + 1) =
      cyclicNorm R A M (n + 1) := by
    rw [← Finset.sum_range_reflect, ← cyclicOperator_mul_cyclicNorm, cyclicNorm_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← pow_succ', show n + 1 - (n + 2 - 1 - j) = j by
      have := Finset.mem_range.1 hj; omega]
  have hb : hochschildCoboundary R A M n φ =
      cyclicNorm R A M (n + 1) (hochschildCoface R A M 0 φ) := by
    rw [hochschildCoboundary_eq_sum, Finset.sum_congr rfl fun j _ ↦ hface j,
      Fin.sum_univ_eq_sum_range (fun j ↦ (cyclicOperator R A M (n + 1) ^ (n + 1 - j + 1))
        (hochschildCoface R A M 0 φ)), ← LinearMap.sum_apply, hsum]
  have hsign : (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (i : ℕ) •
      cyclicNorm R A M (n + 1) (hochschildCoface R A M i φ) =
      cyclicNorm R A M (n + 1) (hochschildCoface R A M i φ) := by
    rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  rw [← hsign, ← map_zsmul (cyclicNorm R A M (n + 1)), hface i, ← Module.End.mul_apply,
    cyclicNorm_mul_cyclicOperator_pow, ← hb]

/-- `b (N φ) = N (δ₀ (N φ))`. -/
private theorem hochschildCoboundary_cyclicNorm
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    hochschildCoboundary R A M n (cyclicNorm R A M n φ) =
      cyclicNorm R A M (n + 1) (hochschildCoface R A M 0 (cyclicNorm R A M n φ)) := by
  simpa using (cyclicNorm_hochschildCoface_of_mem_cyclicCochains
    (cyclicNorm_mem_cyclicCochains φ) 0).symm

variable (R A M n) in
/-- The second commutation relation of the cyclic bicomplex: `b N = N b'`. -/
theorem hochschildCoboundary_comp_cyclicNorm :
    hochschildCoboundary R A M n ∘ₗ cyclicNorm R A M n =
      cyclicNorm R A M (n + 1) ∘ₗ barCoboundary R A M n := by
  ext φ : 1
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hochschildCoboundary_cyclicNorm,
    cyclicNorm_barCoboundary]

end Bar

section BarAssoc

variable {R A M : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- The bar coboundary squares to zero. -/
@[simp]
theorem barCoboundary_barCoboundary (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
    M) :
    barCoboundary R A M (n + 1) (barCoboundary R A M n φ) = 0 := by
  ext a
  simp only [barCoboundary_apply, ← hochschildFace_castSucc, _root_.zero_apply]
  cases n with
  | zero =>
    have h := hochschildFace_hochschildFace (le_refl (0 : Fin 2)) a
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ,
      pow_zero, one_smul, Fin.castSucc_zero, Fin.castSucc_one, Fin.succ_zero_eq_one] at h ⊢
    rw [h]
    simp
  | succ m =>
    exact sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
      (fun i j ↦ φ (hochschildFace j.castSucc (hochschildFace i.castSucc a))) fun i j hij ↦ by
        rw [← Fin.succ_castSucc, hochschildFace_hochschildFace (Fin.castSucc_le_castSucc_iff.2 hij)]

end BarAssoc

/-! ### The contraction of the bar complex and Connes' operator `B` -/

section Contraction

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [One A] [Module R A] [AddCommGroup M]
  [Module R M] [SMulCommClass R R M]

/-- The contraction `s : Cⁿ⁺¹ → Cⁿ` of the bar complex, `(sφ)(a₀, …, aₙ) = φ(1, a₀, …, aₙ)`. -/
def barContraction (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun φ :=
    { toFun a := φ (Fin.cons 1 a)
      map_update_add' := by
        intro _ a k x y
        obtain rfl : ‹DecidableEq (Fin (n + 1))› = instDecidableEqFin _ := Subsingleton.elim _ _
        simp only [Fin.cons_update, MultilinearMap.map_update_add]
      map_update_smul' := by
        intro _ a k c x
        obtain rfl : ‹DecidableEq (Fin (n + 1))› = instDecidableEqFin _ := Subsingleton.elim _ _
        simp only [Fin.cons_update, MultilinearMap.map_update_smul] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {R A M} {n : ℕ}

/-- The contraction evaluates `φ` with `1` inserted as the zeroth argument. -/
@[simp]
theorem barContraction_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M)
    (a : Fin (n + 1) → A) :
    barContraction R A M n φ a = φ (Fin.cons 1 a) :=
  (rfl)

variable (R A M) in
/-- Connes' operator `B = N s (1 - λ) : Cⁿ⁺¹ → Cⁿ` on the cochains of a unital algebra. -/
def connesB (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M :=
  cyclicNorm R A M n ∘ₗ barContraction R A M n ∘ₗ (1 - cyclicOperator R A M (n + 1))

/-- Connes' operator evaluates as `B φ = N (s (φ - λ φ))`. -/
theorem connesB_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M) :
    connesB R A M n φ =
      cyclicNorm R A M n (barContraction R A M n (φ - cyclicOperator R A M (n + 1) φ)) :=
  (rfl)

/-- Connes' operator `B` takes values in the cyclic cochains. -/
theorem connesB_mem_cyclicCochains (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M) :
    connesB R A M n φ ∈ cyclicCochains R A M n :=
  cyclicNorm_mem_cyclicCochains _

/-- Connes' operator `B` vanishes on cyclic cochains. -/
theorem connesB_eq_zero_of_mem_cyclicCochains
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M
        (n + 1)) :
    connesB R A M n φ = 0 := by
  rw [connesB_apply, mem_cyclicCochains_iff_cyclicOperator_apply_eq_self.1 hφ, sub_self, map_zero,
    map_zero]

/-- Connes' operator `B` squares to zero. -/
@[simp]
theorem connesB_connesB (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 3) ↦ A) M) :
    connesB R A M n (connesB R A M (n + 1) φ) = 0 :=
  connesB_eq_zero_of_mem_cyclicCochains (connesB_mem_cyclicCochains φ)

variable (R A M n) in
/-- Connes' operator `B` squares to zero, as a composite of linear maps. -/
theorem connesB_comp_connesB : connesB R A M n ∘ₗ connesB R A M (n + 1) = 0 :=
  LinearMap.ext connesB_connesB

end Contraction

section ConnesB

variable {R A M : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- The contraction `s` is a contracting homotopy of the bar complex in degree zero:
`s (b' φ) = φ`. -/
@[simp]
theorem barContraction_barCoboundary_zero (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ A)
    M) :
    barContraction R A M 0 (barCoboundary R A M 0 φ) = φ := by
  ext a
  simp only [barContraction_apply, barCoboundary_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    ← hochschildFace_castSucc, Fin.castSucc_zero, hochschildFace_zero_cons_one, Fin.val_zero,
    pow_zero, one_smul, add_zero]

/-- The contraction `s` is a contracting homotopy of the bar complex in positive degrees:
`b' (s φ) + s (b' φ) = φ`. -/
theorem barCoboundary_barContraction_add_barContraction_barCoboundary
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M) :
    barCoboundary R A M n (barContraction R A M n φ) +
      barContraction R A M (n + 1) (barCoboundary R A M (n + 1) φ) = φ := by
  ext a
  simp only [_root_.add_apply, barCoboundary_apply, barContraction_apply]
  rw [Fin.sum_univ_succ (n := n + 1)]
  simp only [← hochschildFace_castSucc, hochschildFace_succ_castSucc_cons, Fin.val_zero,
    Fin.val_succ, pow_zero, one_smul, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
  rw [Fin.castSucc_zero, hochschildFace_zero_cons_one]
  abel

/-- Connes' operator `B` anticommutes with the Hochschild coboundary: `b (B φ) + B (b φ) = 0`. -/
theorem hochschildCoboundary_connesB_add_connesB_hochschildCoboundary
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M) :
    hochschildCoboundary R A M n (connesB R A M n φ) +
      connesB R A M (n + 1) (hochschildCoboundary R A M (n + 1) φ) = 0 := by
  have hN := LinearMap.congr_fun (hochschildCoboundary_comp_cyclicNorm R A M n)
    (barContraction R A M n (φ - cyclicOperator R A M (n + 1) φ))
  have hcyc :=
    LinearMap.congr_fun (one_sub_cyclicOperator_comp_hochschildCoboundary R A M (n + 1)) φ
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply] at hN hcyc
  rw [connesB_apply, connesB_apply, hN, hcyc, ← map_add,
    barCoboundary_barContraction_add_barContraction_barCoboundary, map_sub,
    ← Module.End.mul_apply, cyclicNorm_mul_cyclicOperator, sub_self]

variable (R A M n) in
/-- Connes' operator `B` anticommutes with the Hochschild coboundary, as linear maps:
`b B + B b = 0`. -/
theorem hochschildCoboundary_comp_connesB_add_connesB_comp_hochschildCoboundary :
    hochschildCoboundary R A M n ∘ₗ connesB R A M n +
      connesB R A M (n + 1) ∘ₗ hochschildCoboundary R A M (n + 1) = 0 :=
  LinearMap.ext hochschildCoboundary_connesB_add_connesB_hochschildCoboundary

/-- The mixed-complex identity at the bottom degree: `B (b φ) = 0` for every degree-zero
cochain `φ`. -/
@[simp]
theorem connesB_hochschildCoboundary_zero (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ A)
    M) :
    connesB R A M 0 (hochschildCoboundary R A M 0 φ) = 0 :=
  connesB_eq_zero_of_mem_cyclicCochains (hochschildCoboundary_mem_cyclicCochains R A M (by simp))

end ConnesB

end TauCeti
