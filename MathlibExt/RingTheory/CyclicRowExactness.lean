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
TauCeti/RingTheory/CyclicCohomology/RowExactness.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import MathlibExt.RingTheory.ConnesOperator
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Projection

/-!
# Split exactness of the rows of the cyclic bicomplex

In degree `n`, write `λ` for the signed cyclic operator and `N = 1 + λ + ⋯ + λⁿ`.
Without any invertibility hypothesis, the unscaled row homotopy
`H' = ∑ j ≤ n, ∑ k < j, λᵏ` (`TauCeti.cyclicRowHomotopySum`) satisfies
`(1 - λ) H' = H' (1 - λ) = (n + 1) - N`.
When `n + 1` is invertible in the commutative coefficient semiring, averaging gives a projection
`P = N / (n + 1)` onto the cyclic cochains, and the scaled operator
`H = H' / (n + 1)` (`TauCeti.cyclicRowHomotopy`) satisfies
`(1 - λ) H = H (1 - λ) = 1 - P`.

Consequently the row alternating between `1 - λ` and `N` is exact at both kinds
of terms: `range N = ker (1 - λ)` and `range (1 - λ) = ker N`.
These explicit splittings are used to compare the cyclic cochain complex with
the total cyclic bicomplex. No multiplication or unit on the argument module is
needed for these horizontal identities.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.
-/

public section

namespace TauCeti

-- Scaling cochain endomorphisms requires commuting scalar actions on the cochain module.
-- Mathlib supplies these instances here for commutative coefficient semirings.
variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M] {n : ℕ}

variable (R A M n) in
/-- The unscaled cyclic row homotopy `H' = ∑_{j ≤ n} ∑_{k < j} λᵏ` on `n`-cochains. When `n + 1` is
invertible in `R`, `TauCeti.cyclicRowHomotopy` is `⅟(n + 1 : R) • cyclicRowHomotopySum`. -/
def cyclicRowHomotopySum :
    Module.End R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :=
  ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range j, cyclicOperator R A M n ^ k

variable (R A M n) in
/-- The explicit finite-sum formula for the unscaled cyclic row homotopy. -/
theorem cyclicRowHomotopySum_def :
    cyclicRowHomotopySum R A M n =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range j, cyclicOperator R A M n ^ k :=
  (rfl)

/-- `(1 - λ) H' = (n + 1) - N` on `n`-cochains, without any invertibility hypothesis on `R`. -/
theorem one_sub_cyclicOperator_mul_cyclicRowHomotopySum :
    (1 - cyclicOperator R A M n) * cyclicRowHomotopySum R A M n =
      (n + 1 : R) • 1 - cyclicNorm R A M n := by
  rw [cyclicRowHomotopySum, Finset.mul_sum]
  simp only [mul_neg_geom_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← cyclicNorm_def]
  simp [← Nat.cast_smul_eq_nsmul R]

/-- `H' (1 - λ) = (n + 1) - N` on `n`-cochains, without any invertibility hypothesis on `R`. -/
theorem cyclicRowHomotopySum_mul_one_sub_cyclicOperator :
    cyclicRowHomotopySum R A M n * (1 - cyclicOperator R A M n) =
      (n + 1 : R) • 1 - cyclicNorm R A M n := by
  rw [cyclicRowHomotopySum, Finset.sum_mul]
  simp only [geom_sum_mul_neg, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← cyclicNorm_def]
  simp [← Nat.cast_smul_eq_nsmul R]

/-- Pointwise form of `one_sub_cyclicOperator_mul_cyclicRowHomotopySum`. -/
theorem one_sub_cyclicOperator_apply_cyclicRowHomotopySum
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    (1 - cyclicOperator R A M n) (cyclicRowHomotopySum R A M n φ) =
      (n + 1 : R) • φ - cyclicNorm R A M n φ := by
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] using
    LinearMap.congr_fun one_sub_cyclicOperator_mul_cyclicRowHomotopySum φ

/-- Pointwise form of `cyclicRowHomotopySum_mul_one_sub_cyclicOperator`. -/
theorem cyclicRowHomotopySum_apply_one_sub_cyclicOperator
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicRowHomotopySum R A M n ((1 - cyclicOperator R A M n) φ) =
      (n + 1 : R) • φ - cyclicNorm R A M n φ := by
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] using
    LinearMap.congr_fun cyclicRowHomotopySum_mul_one_sub_cyclicOperator φ

variable [Invertible (n + 1 : R)]

variable (R A M n) in
/-- Averaging over cyclic rotations projects onto the cyclic cochains. -/
noncomputable def cyclicAverage :
    Module.End R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :=
  ⅟(n + 1 : R) • cyclicNorm R A M n

/-- The cyclic average is the cyclic norm divided by the number of arguments. -/
-- Keep averaging intact under simplification so its projection identities remain normal forms.
theorem cyclicAverage_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicAverage R A M n φ = ⅟(n + 1 : R) • cyclicNorm R A M n φ := (rfl)

/-- Averaging takes values in the cyclic cochains. -/
theorem cyclicAverage_mem_cyclicCochains
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicAverage R A M n φ ∈ cyclicCochains R A M n :=
  (cyclicCochains R A M n).smul_mem _ (cyclicNorm_mem_cyclicCochains φ)

/-- Averaging fixes every cyclic cochain. -/
theorem cyclicAverage_apply_of_mem_cyclicCochains
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ cyclicCochains R A M n) : cyclicAverage R A M n φ = φ := by
  rw [cyclicAverage_apply, cyclicNorm_apply_of_mem_cyclicCochains hφ,
    invOf_smul_smul]

/-- The cyclic average is idempotent. -/
@[simp]
theorem cyclicAverage_cyclicAverage
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicAverage R A M n (cyclicAverage R A M n φ) = cyclicAverage R A M n φ :=
  cyclicAverage_apply_of_mem_cyclicCochains
    (cyclicAverage_mem_cyclicCochains φ)

/-- The cyclic average is an idempotent endomorphism. -/
theorem isIdempotentElem_cyclicAverage : IsIdempotentElem (cyclicAverage R A M n) :=
  LinearMap.ext cyclicAverage_cyclicAverage

/-- The cyclic average absorbs itself under composition. -/
@[simp]
theorem cyclicAverage_mul_cyclicAverage :
    cyclicAverage R A M n * cyclicAverage R A M n = cyclicAverage R A M n :=
  isIdempotentElem_cyclicAverage.eq

/-- The cyclic average absorbs the cyclic operator on the left: `λ P = P`. -/
@[simp]
theorem cyclicOperator_mul_cyclicAverage :
    cyclicOperator R A M n * cyclicAverage R A M n = cyclicAverage R A M n := by
  rw [cyclicAverage, mul_smul_comm, cyclicOperator_mul_cyclicNorm]

/-- The cyclic average absorbs the cyclic operator on the right: `P λ = P`. -/
@[simp]
theorem cyclicAverage_mul_cyclicOperator :
    cyclicAverage R A M n * cyclicOperator R A M n = cyclicAverage R A M n := by
  rw [cyclicAverage, smul_mul_assoc, cyclicNorm_mul_cyclicOperator]

/-- Averaging and the cyclic norm have the same kernel. -/
@[simp]
theorem ker_cyclicAverage :
    LinearMap.ker (cyclicAverage R A M n) = LinearMap.ker (cyclicNorm R A M n) := by
  ext φ
  simp only [LinearMap.mem_ker, cyclicAverage_apply, invOf_smul_eq_iff, smul_zero]

/-- The image of averaging is exactly the cyclic cochains. -/
theorem range_cyclicAverage :
    LinearMap.range (cyclicAverage R A M n) = cyclicCochains R A M n :=
  LinearMap.IsProj.range ⟨cyclicAverage_mem_cyclicCochains,
    fun _ hφ ↦ cyclicAverage_apply_of_mem_cyclicCochains hφ⟩

variable (R A M n) in
/-- The cyclic row homotopy. Its product with `1 - λ` on either side is `1 - P`,
where `P` is cyclic averaging. -/
noncomputable def cyclicRowHomotopy :
    Module.End R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :=
  ⅟(n + 1 : R) • cyclicRowHomotopySum R A M n

variable (R A M n) in
/-- The explicit finite-sum formula for the cyclic row homotopy. -/
theorem cyclicRowHomotopy_def :
    cyclicRowHomotopy R A M n = ⅟(n + 1 : R) •
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range j, cyclicOperator R A M n ^ k :=
  (rfl)

/-- The row homotopy splits `1 - λ` on the left, up to the cyclic projection. -/
theorem one_sub_cyclicOperator_mul_cyclicRowHomotopy :
    (1 - cyclicOperator R A M n) * cyclicRowHomotopy R A M n =
      1 - cyclicAverage R A M n := by
  rw [cyclicRowHomotopy, mul_smul_comm, one_sub_cyclicOperator_mul_cyclicRowHomotopySum,
    smul_sub, invOf_smul_smul, cyclicAverage]

/-- The row homotopy splits `1 - λ` on the right, up to the cyclic projection. -/
theorem cyclicRowHomotopy_mul_one_sub_cyclicOperator :
    cyclicRowHomotopy R A M n * (1 - cyclicOperator R A M n) =
      1 - cyclicAverage R A M n := by
  rw [cyclicRowHomotopy, smul_mul_assoc, cyclicRowHomotopySum_mul_one_sub_cyclicOperator,
    smul_sub, invOf_smul_smul, cyclicAverage]

/-- Applying the row homotopy gives a preimage of `φ - P φ` under `1 - λ`. -/
theorem one_sub_cyclicOperator_apply_cyclicRowHomotopy
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    (1 - cyclicOperator R A M n) (cyclicRowHomotopy R A M n φ) =
      φ - cyclicAverage R A M n φ := by
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] using
    LinearMap.congr_fun one_sub_cyclicOperator_mul_cyclicRowHomotopy φ

/-- The cyclic norm surjects onto the cyclic cochains. -/
theorem range_cyclicNorm :
    LinearMap.range (cyclicNorm R A M n) = cyclicCochains R A M n := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    exact cyclicNorm_mem_cyclicCochains φ
  · intro φ hφ
    refine ⟨⅟(n + 1 : R) • φ, ?_⟩
    rw [map_smul, cyclicNorm_apply_of_mem_cyclicCochains hφ, invOf_smul_smul]

/-- Exactness of a cyclic-bicomplex row at a term following `N`. -/
theorem range_cyclicNorm_eq_ker_one_sub_cyclicOperator :
    LinearMap.range (cyclicNorm R A M n) =
      LinearMap.ker (1 - cyclicOperator R A M n) := by
  rw [range_cyclicNorm, ker_one_sub_cyclicOperator]

/-- Exactness of a cyclic-bicomplex row at a term following `1 - λ`.
For a cochain killed by `N`, the row homotopy gives an explicit preimage. -/
theorem range_one_sub_cyclicOperator_eq_ker_cyclicNorm :
    LinearMap.range (1 - cyclicOperator R A M n) =
      LinearMap.ker (cyclicNorm R A M n) := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [← Module.End.mul_apply, cyclicNorm_mul_cyclicOperator, sub_self]
  · intro φ hφ
    refine ⟨cyclicRowHomotopy R A M n φ, ?_⟩
    rw [one_sub_cyclicOperator_apply_cyclicRowHomotopy, cyclicAverage_apply,
      LinearMap.mem_ker.1 hφ, smul_zero, sub_zero]

end TauCeti
