/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.FiniteSupportLengthEuler
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Page length Euler invariance

For a homological spectral sequence of modules over a commutative ring,
suppose the second page is zero outside a finite rectangle and its modules
inside the rectangle have finite length. These two properties persist on
every later page, and the signed length sum over the rectangle is invariant.
Each page differential lowers total degree by one, so the differential-image
contributions cancel. The hypotheses concern the second page; no finite-length
condition is imposed on first-page modules or underlying bicomplex terms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory.Limits
open scoped BigOperators

universe u v

namespace CategoryTheory.SpectralSequence

variable {R : Type u} [CommRing R]
  (E : SpectralSequence (ModuleCat.{v} R)
    (fun r : ℤ => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1)

/-- For a homological spectral sequence `E` of modules over a commutative ring
`R` and page `r ≥ 1`, the integer Euler sum over `0 ≤ p ≤ m`, `0 ≤ q ≤ n`,
with summand `(-1)^(p+q) * (Module.length R ((E.page r hr).X (p,q))).toNat`.
The definition uses `Module.length.toNat`; the invariance theorems require
finite module lengths and vanishing outside this rectangle. -/
def lengthEuler (r : ℤ) (hr : 1 ≤ r) (m n : ℕ) : ℤ :=
  ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (p + q) * (Module.length R ((E.page r hr).X (p, q))).toNat

/-- Let `E` be a homological spectral sequence of modules over a commutative
ring `R`. If page `r ≥ 1` vanishes whenever `p > m` or `q > n`, and every module
inside `0 ≤ p ≤ m`, `0 ≤ q ≤ n` has finite `R`-length, page `r + 1` has
the same support bound and finite-length property, and its rectangle Euler
sum equals that of page `r`. The page differential lowers `p + q` by one. -/
theorem lengthEuler_succ (r : ℤ) (hr : 1 ≤ r) (m n : ℕ)
    (hlen : ∀ p ≤ m, ∀ q ≤ n, Module.length R ((E.page r hr).X (p, q)) ≠ ⊤)
    (hzero : ∀ p q, m < p ∨ n < q → IsZero ((E.page r hr).X (p, q))) :
    (∀ p ≤ m, ∀ q ≤ n,
      Module.length R ((E.page (r + 1) (by omega)).X (p, q)) ≠ ⊤) ∧
    (∀ p q, m < p ∨ n < q → IsZero ((E.page (r + 1) (by omega)).X (p, q))) ∧
    E.lengthEuler (r + 1) (by omega) m n = E.lengthEuler r hr m n := by
  let s := Finset.range (m + 1) ×ˢ Finset.range (n + 1)
  let ε (pq : ℕ × ℕ) : ℤ := (-1 : ℤ) ^ (pq.1 + pq.2)
  have hs0 (pq : ℕ × ℕ) (hpq : pq ∉ s) : IsZero ((E.page r hr).X pq) := by
    simp only [s, Finset.mem_product, Finset.mem_range] at hpq
    exact hzero pq.1 pq.2 (by omega)
  have hslen (pq : ℕ × ℕ) (hpq : pq ∈ s) :
      Module.length R ((E.page r hr).X pq) ≠ ⊤ := by
    simp only [s, Finset.mem_product, Finset.mem_range] at hpq
    exact hlen pq.1 (by omega) pq.2 (by omega)
  have hε (pq pq' : ℕ × ℕ)
      (h : (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq pq') :
      ε pq + ε pq' = 0 := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    have hd : pq.1 + pq.2 = pq'.1 + pq'.2 + 1 := by omega
    dsimp only [ε]
    rw [hd, pow_succ, mul_neg_one, neg_add_cancel]
  obtain ⟨hfin, hzH, he⟩ := (E.page r hr).lengthEuler_eq_homology_of_finite_support
    s ε hs0 hslen hε
  constructor
  · intro p hp q hq
    rw [← (E.iso r (r + 1) (p, q) rfl hr).toLinearEquiv.length_eq]
    exact hfin (p, q) (by simp only [s, Finset.mem_product, Finset.mem_range]; omega)
  constructor
  · intro p q h
    exact (hzH (p, q) (by simp only [s, Finset.mem_product, Finset.mem_range]; omega)).of_iso
      (E.iso r (r + 1) (p, q) rfl hr).symm
  · have hNext : E.lengthEuler (r + 1) (by omega) m n =
        ∑ pq ∈ s, ε pq * (Module.length R ((E.page r hr).homology pq)).toNat := by
      simp only [lengthEuler, s, ε, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [← (E.iso r (r + 1) (p, q) rfl hr).toLinearEquiv.length_eq]
    have hCurrent : E.lengthEuler r hr m n =
        ∑ pq ∈ s, ε pq * (Module.length R ((E.page r hr).X pq)).toNat := by
      simp only [lengthEuler, s, ε, Finset.sum_product]
    exact hNext.trans (he.symm.trans hCurrent.symm)

/-- Let `E` be a homological spectral sequence of modules over a commutative
ring `R`. Assume the second page vanishes whenever `p > m` or `q > n`, and all
its modules in `0 ≤ p ≤ m`, `0 ≤ q ≤ n` have finite `R`-length. For every
`t : ℕ`, page `t + 2` has the same support bound and finite-length property,
and its rectangle Euler sum equals the second-page sum. -/
theorem lengthEuler_from_secondPage (m n : ℕ)
    (hlen : ∀ p ≤ m, ∀ q ≤ n, Module.length R ((E.page 2 (by omega)).X (p, q)) ≠ ⊤)
    (hzero : ∀ p q, m < p ∨ n < q → IsZero ((E.page 2 (by omega)).X (p, q))) (t : ℕ) :
    (∀ p ≤ m, ∀ q ≤ n,
      Module.length R ((E.page ((t : ℤ) + 2) (by omega)).X (p, q)) ≠ ⊤) ∧
    (∀ p q, m < p ∨ n < q → IsZero ((E.page ((t : ℤ) + 2) (by omega)).X (p, q))) ∧
    E.lengthEuler ((t : ℤ) + 2) (by omega) m n = E.lengthEuler 2 (by omega) m n := by
  induction t with
  | zero => exact ⟨hlen, hzero, rfl⟩
  | succ t ih =>
    have h := E.lengthEuler_succ ((t : ℤ) + 2) (by omega) m n ih.1 ih.2.1
    have ht : (((t + 1 : ℕ) : ℤ) + 2) = ((t : ℤ) + 2) + 1 := by omega
    constructor
    · intro p hp q hq
      rw [← (E.pageXIsoOfEq (p, q) (((t : ℤ) + 2) + 1)
        (((t + 1 : ℕ) : ℤ) + 2) ht.symm (by omega)).toLinearEquiv.length_eq]
      exact h.1 p hp q hq
    constructor
    · intro p q hpq
      exact (h.2.1 p q hpq).of_iso
        (E.pageXIsoOfEq (p, q) (((t : ℤ) + 2) + 1)
          (((t + 1 : ℕ) : ℤ) + 2) ht.symm (by omega)).symm
    · simpa only [ht] using h.2.2.trans ih.2.2

end CategoryTheory.SpectralSequence
