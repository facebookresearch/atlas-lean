/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Finite arithmetic discrepancy and positive-index convolution

Finite arithmetic sequences are ordinary `Finsupp`s, with index zero discarded.
Discrepancy supports real or complex coefficients. Multiplicative convolution
uses Mathlib's monoid-algebra product, not additive convolution or supplied data.
Primitive-residue maxima have intrinsically positive moduli.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeDistribution

/-- Signed residue discrepancy, normalized by the totient of a positive modulus over a
characteristic-zero field, so the normalizing cast is nonzero. Only positive indices
contribute. Modulus zero is unrepresentable: `q` ranges over `ℕ+`. -/
noncomputable def discrepancy {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : ℕ →₀ 𝕜)
    (q : ℕ+) (a : ℕ) : 𝕜 :=
  α.sum (fun n v ↦ if 0 < n ∧ n % q = a % q then v else 0) -
    α.sum (fun n v ↦ if 0 < n ∧ Nat.Coprime n q then v else 0) / (Nat.totient (q : ℕ) : 𝕜)

/-- The extra index zero contributes nothing to discrepancy over any coefficient field. -/
@[simp] theorem discrepancy_single_zero {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (v : 𝕜)
    (q : ℕ+) (a : ℕ) :
    discrepancy (Finsupp.single 0 v) q a = 0 := by
  simp [discrepancy]

/-- A positive singleton contributes its residue value minus the coprime mean. -/
theorem discrepancy_single {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (n : ℕ) (hn : 0 < n)
    (v : 𝕜) (q : ℕ+) (a : ℕ) :
    discrepancy (Finsupp.single n v) q a =
      (if n % q = a % q then v else 0) -
        (if Nat.Coprime n q then v else 0) / (Nat.totient (q : ℕ) : 𝕜) := by
  simp [discrepancy, hn]

/-- The finite maximum over all primitive residue classes of a positive modulus. -/
noncomputable def primitiveDiscrepancy (α : ℕ →₀ ℝ) (q : ℕ+) : ℝ :=
  ⨆ a : (ZMod (q : ℕ))ˣ, |discrepancy α q a.val.val|

/-- A primitive-residue maximum is attained because the positive modulus is finite. -/
theorem primitiveDiscrepancy_attained (α : ℕ →₀ ℝ) (q : ℕ+) :
    ∃ a : (ZMod (q : ℕ))ˣ, primitiveDiscrepancy α q = |discrepancy α q a.val.val| := by
  let : NeZero (q : ℕ) := ⟨ne_of_gt q.pos⟩
  obtain ⟨a, ha⟩ := Finite.ciSup_mem (fun a : (ZMod (q : ℕ))ˣ ↦
    |discrepancy α q a.val.val|)
  exact ⟨a, ha.symm⟩

/-- Each primitive-residue discrepancy is bounded by that finite maximum. -/
theorem abs_discrepancy_le_primitiveDiscrepancy (α : ℕ →₀ ℝ) (q : ℕ+)
    (a : (ZMod (q : ℕ))ˣ) : |discrepancy α q a.val.val| ≤ primitiveDiscrepancy α q := by
  let : NeZero (q : ℕ) := ⟨ne_of_gt q.pos⟩
  exact le_ciSup (Set.finite_range (fun a : (ZMod (q : ℕ))ˣ ↦
    |discrepancy α q a.val.val|)).bddAbove a

/-- The sum of primitive-residue discrepancies over positive moduli at most `Q`. -/
noncomputable def averagedDiscrepancy (α : ℕ →₀ ℝ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, if h : 0 < q then primitiveDiscrepancy α ⟨q, h⟩ else 0

/-- There are no positive moduli below the cutoff zero. -/
@[simp] theorem averagedDiscrepancy_zero (α : ℕ →₀ ℝ) : averagedDiscrepancy α 0 = 0 := by
  simp [averagedDiscrepancy]

/-- Finite multiplicative convolution after normalizing both sequences at index zero. -/
noncomputable def convolution {R : Type*} [Semiring R] (α β : ℕ →₀ R) : ℕ →₀ R :=
  (MonoidAlgebra.ofCoeff (α.filter (fun n ↦ 0 < n)) *
    MonoidAlgebra.ofCoeff (β.filter (fun n ↦ 0 < n)) : MonoidAlgebra R ℕ).coeff

/-- The coefficient is the finite sum over positive factors whose product is `n`. -/
theorem convolution_apply {R : Type*} [Semiring R] (α β : ℕ →₀ R) (n : ℕ) :
    convolution α β n =
      (α.filter (fun a ↦ 0 < a)).sum (fun a u ↦
        (β.filter (fun b ↦ 0 < b)).sum (fun b v ↦ if a * b = n then u * v else 0)) :=
  MonoidAlgebra.coeff_mul _ _ _

/-- A positive-index convolution has coefficient zero at index zero. -/
@[simp] theorem convolution_apply_zero {R : Type*} [Semiring R] (α β : ℕ →₀ R) :
    convolution α β 0 = 0 := by
  rw [convolution_apply, Finsupp.sum_filter_index]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finsupp.sum_filter_index]
  apply Finset.sum_eq_zero
  intro b hb
  have ha_pos : 0 < a := by
    rw [Finsupp.support_filter] at ha
    exact (Finset.mem_filter.mp ha).2
  have hb_pos : 0 < b := by
    rw [Finsupp.support_filter] at hb
    exact (Finset.mem_filter.mp hb).2
  simp [Nat.ne_of_gt ha_pos, Nat.ne_of_gt hb_pos]

/-- A sequence supported only at the discarded index contributes no convolution. -/
@[simp] theorem convolution_single_zero_left {R : Type*} [Semiring R]
    (v : R) (β : ℕ →₀ R) : convolution (Finsupp.single 0 v) β = 0 := by
  simp [convolution]

/-- The zero-index normalization applies to the second factor as well. -/
@[simp] theorem convolution_single_zero_right {R : Type*} [Semiring R]
    (α : ℕ →₀ R) (v : R) : convolution α (Finsupp.single 0 v) = 0 := by
  simp [convolution]

/-- The actual von Mangoldt function on the positive closed dyadic interval.
Source: Polymath8b v4, Claim 2.2 and the positive-integer convention before Definition 1.6. -/
noncomputable def dyadicVonMangoldt (x : ℝ) : ℕ →₀ ℝ :=
  Finsupp.onFinset (Finset.Icc 1 ⌊2 * x⌋₊)
    (fun n ↦ if n ∈ Finset.Icc 1 ⌊2 * x⌋₊ ∧ x ≤ (n : ℝ) then
      ArithmeticFunction.vonMangoldt n else 0)
    (by intro n; contrapose!; simp_all)

/-- The finite cutoff gives exactly the source's two closed real endpoints.
Source: Polymath8b v4, Claim 2.2. -/
theorem dyadicVonMangoldt_apply (x : ℝ) (hx : 0 < x) (n : ℕ) :
    dyadicVonMangoldt x n =
      if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then ArithmeticFunction.vonMangoldt n else 0 := by
  unfold dyadicVonMangoldt
  rw [Finsupp.onFinset_apply]
  congr 1
  apply propext
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hfloor⟩, hxle⟩
    exact ⟨hxle, (Nat.cast_le.mpr hfloor).trans (Nat.floor_le (by positivity))⟩
  · rintro ⟨hxle, hnle⟩
    have hn : 1 ≤ n := by
      by_contra h
      have hn0 : n = 0 := by omega
      simp [hn0] at hxle
      linarith
    exact ⟨⟨hn, Nat.le_floor hnle⟩, hxle⟩

end MathlibExt.NumberTheory.PrimeDistribution
