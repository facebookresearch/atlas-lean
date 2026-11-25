/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/asgard-lean, commit
e5e098d5bce80c3907a6acd4e2beb904309a1709,
`Gimle/Asgard/Streams/Causal.lean` and `Gimle/Asgard/Streams/Core.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Tactic.FieldSimp

/-!
# Formal causal differential equations

A right-hand side is causal along an axis if coefficients through axis degree k
read only input coefficients through degree k. Integration raises agreement by
one degree, so Picard iteration stabilizes coefficient by coefficient. It gives
exactly one formal solution over a characteristic-zero field with the prescribed
entire degree-zero slice.
Spatial derivatives and products preserve causality. This is formal Picard
existence and uniqueness; no convergence or analytic solution is asserted.

Mathematical reference: A. Luzón, M. A. Morón and J. L. Ramírez,
Differential equations in Ward's calculus, Section 2 and Theorem 11,
https://arxiv.org/abs/2408.12552. For the ordinary derivative, the source uses
nonexpansiveness in the degree metric and contracting formal integration.
Here the same coefficient-stabilization argument uses degree in one selected
axis, allowing arbitrary remaining formal variables and a full boundary slice.
This selected-axis version is an extension of the source's univariate statement.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ K : Type*} [Field K]

private lemma add_single_one_eq_update (n : σ →₀ ℕ) (i : σ) :
    n + Finsupp.single i 1 = n.update i (n i + 1) := by
  classical
  ext j
  by_cases h : j = i <;> simp [h, Finsupp.update_apply]

/-- Formal integration along one axis. The entire zero slice comes from b;
positive-axis coefficients of b do not enter the result. -/
noncomputable def pIntegral (i : σ) (f b : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun n => if n i = 0 then coeff n b else coeff (n.update i (n i - 1)) f / (n i : K)

@[simp] theorem coeff_pIntegral (i : σ) (f b : MvPowerSeries σ K) (n : σ →₀ ℕ) :
    coeff n (pIntegral i f b) =
      if n i = 0 then coeff n b else coeff (n.update i (n i - 1)) f / (n i : K) := rfl

/-- Differentiating the formal integral recovers the integrand. -/
@[simp] theorem pderiv_pIntegral [CharZero K] (i : σ) (f b : MvPowerSeries σ K) :
    pderiv i (pIntegral i f b) = f := by
  classical
  ext n
  rw [coeff_pderiv, add_single_one_eq_update, coeff_pIntegral]
  simp only [Finsupp.coe_update, Function.update_self, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel_right, Finsupp.update_idem, Finsupp.update_self]
  have hn : (n i : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n i)
  push_cast
  exact div_mul_cancel₀ _ hn

/-- Integration of the derivative reconstructs a series from its zero slice. -/
@[simp] theorem pIntegral_pderiv [CharZero K] (i : σ) (f : MvPowerSeries σ K) :
    pIntegral i (pderiv i f) f = f := by
  classical
  ext n
  rw [coeff_pIntegral]
  split_ifs with hn
  · rfl
  · rw [coeff_pderiv, add_single_one_eq_update]
    have hpos : 1 ≤ n i := Nat.one_le_iff_ne_zero.mpr hn
    have hc : (n i : K) ≠ 0 := by exact_mod_cast hn
    simp only [Finsupp.coe_update, Function.update_self, Finsupp.update_idem,
      Nat.sub_add_cancel hpos, Finsupp.update_self]
    rw [show (↑(n i - 1) : K) + 1 = n i by exact_mod_cast Nat.sub_add_cancel hpos]
    exact mul_div_cancel_right₀ _ hc

namespace Causal

/-- Agreement through degree k on a selected axis, with no restriction on the
other degrees. -/
def Agree (i : σ) (k : ℕ) (a b : MvPowerSeries σ K) : Prop :=
  ∀ n : σ →₀ ℕ, n i ≤ k → coeff n a = coeff n b

/-- A right-hand side reads no higher degree on its selected axis. -/
def IsCausal (i : σ) (F : MvPowerSeries σ K → MvPowerSeries σ K) : Prop :=
  ∀ k a b, Agree i k a b → Agree i k (F a) (F b)

lemma Agree.refl (i : σ) (k : ℕ) (a : MvPowerSeries σ K) : Agree i k a a := fun _ _ => rfl
lemma Agree.symm {i : σ} {k : ℕ} {a b : MvPowerSeries σ K} (h : Agree i k a b) :
    Agree i k b a := fun n hn => (h n hn).symm
lemma Agree.trans {i : σ} {k : ℕ} {a b c : MvPowerSeries σ K}
    (h : Agree i k a b) (h' : Agree i k b c) : Agree i k a c :=
  fun n hn => (h n hn).trans (h' n hn)
lemma Agree.mono {i : σ} {k l : ℕ} {a b : MvPowerSeries σ K}
    (h : Agree i k a b) (hl : l ≤ k) : Agree i l a b := fun n hn => h n (hn.trans hl)
lemma Agree.eq {i : σ} {a b : MvPowerSeries σ K} (h : ∀ k, Agree i k a b) : a = b := by
  classical
  ext n
  exact h (n i) n le_rfl

/-- Addition preserves degree agreement. -/
lemma Agree.add {i : σ} {k : ℕ} {a a' b b' : MvPowerSeries σ K}
    (ha : Agree i k a a') (hb : Agree i k b b') : Agree i k (a + b) (a' + b') := by
  classical
  intro n hn
  simp only [map_add, ha n hn, hb n hn]

/-- Cauchy products read only degrees up to that of the output. -/
lemma Agree.mul {i : σ} {k : ℕ} {a a' b b' : MvPowerSeries σ K}
    (ha : Agree i k a a') (hb : Agree i k b b') : Agree i k (a * b) (a' * b') := by
  classical
  intro n hn
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have he := congrArg (fun q : σ →₀ ℕ => q i) (Finset.mem_antidiagonal.mp hp)
  simp only [Finsupp.add_apply] at he
  rw [ha p.1 (by omega), hb p.2 (by omega)]

/-- Differentiating another axis does not read higher degrees on this axis. -/
lemma Agree.pderiv {i j : σ} (hji : j ≠ i) {k : ℕ} {a b : MvPowerSeries σ K}
    (h : Agree i k a b) : Agree i k (pderiv j a) (pderiv j b) := by
  classical
  intro n hn
  rw [coeff_pderiv, coeff_pderiv, h _ (by simpa [Finsupp.single_eq_of_ne hji.symm] using hn)]

/-- Integration raises degree agreement and reads only the zero boundary slice. -/
lemma Agree.pIntegral {i : σ} {k : ℕ} {a b c d : MvPowerSeries σ K}
    (h : Agree i k a b) (hc : Agree i 0 c d) :
    Agree i (k + 1) (pIntegral i a c) (pIntegral i b d) := by
  classical
  intro n hn
  rw [coeff_pIntegral, coeff_pIntegral]
  split_ifs with hz
  · exact hc n hz.le
  · rw [h _ (by simp only [Finsupp.coe_update, Function.update_self]; omega)]

private lemma integral_slice (i : σ) (a b : MvPowerSeries σ K) :
    Agree i 0 (pIntegral i a b) b := by
  classical
  intro n hn
  simp [Nat.le_zero.mp hn]

/-- Picard iterates along the distinguished formal axis. -/
noncomputable def approx (i : σ) (F : MvPowerSeries σ K → MvPowerSeries σ K)
    (boundary : MvPowerSeries σ K) : ℕ → MvPowerSeries σ K
  | 0 => boundary
  | n + 1 => pIntegral i (F (approx i F boundary n)) boundary

/-- The stabilized coefficient at each degree, read from its Picard iterate. -/
noncomputable def solution (i : σ) (F : MvPowerSeries σ K → MvPowerSeries σ K)
    (boundary : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun n => coeff n (approx i F boundary (n i))

variable {i : σ} {F : MvPowerSeries σ K → MvPowerSeries σ K}
  {boundary : MvPowerSeries σ K}

private lemma approx_succ_agree (hF : IsCausal i F) (n : ℕ) :
    Agree i n (approx i F boundary n) (approx i F boundary (n + 1)) := by
  classical
  induction n with
  | zero => exact (integral_slice _ _ _).symm
  | succ n ih => exact (hF n _ _ ih).pIntegral (Agree.refl _ _ _)

/-- Later iterates preserve every coefficient already determined. -/
theorem approx_agree (hF : IsCausal i F) {n m : ℕ} (hnm : n ≤ m) :
    Agree i n (approx i F boundary n) (approx i F boundary m) := by
  classical
  induction m, hnm using Nat.le_induction with
  | base => exact Agree.refl _ _ _
  | succ m hnm ih => exact ih.trans ((approx_succ_agree hF m).mono hnm)

/-- The nth iterate agrees with the solution through degree n. -/
theorem solution_agree (hF : IsCausal i F) (n : ℕ) :
    Agree i n (approx i F boundary n) (solution i F boundary) := by
  classical
  intro m hm
  exact (approx_agree hF hm m le_rfl).symm

/-- The entire degree-zero slice, not just the constant coefficient, is fixed. -/
theorem solution_slice (n : σ →₀ ℕ) (hn : n i = 0) :
    coeff n (solution i F boundary) = coeff n boundary := by
  classical
  change coeff n (approx i F boundary (n i)) = _
  rw [hn]
  rfl

private theorem solution_reconstructs (hF : IsCausal i F) :
    pIntegral i (F (solution i F boundary)) boundary = solution i F boundary := by
  classical
  apply Agree.eq (i := i)
  intro k
  cases k with
  | zero =>
      exact (integral_slice _ _ _).trans (solution_agree hF 0)
  | succ n =>
      have step := (hF n _ _ (solution_agree (boundary := boundary) hF n)).pIntegral
        (Agree.refl i 0 boundary)
      exact step.symm.trans (solution_agree hF (n + 1))

/-- The stabilized Picard iterates solve the formal differential equation. -/
theorem solution_pde [CharZero K] (hF : IsCausal i F) :
    pderiv i (solution i F boundary) = F (solution i F boundary) := by
  classical
  conv_lhs => rw [← solution_reconstructs hF]
  exact pderiv_pIntegral _ _ _

/-- Formal uniqueness from the equation and the entire zero slice. -/
theorem formal_unique [CharZero K] (hF : IsCausal i F) (a b : MvPowerSeries σ K)
    (ha : pderiv i a = F a) (hb : pderiv i b = F b) (hs : Agree i 0 a b) : a = b := by
  classical
  apply Agree.eq (i := i)
  intro k
  induction k with
  | zero => exact hs
  | succ k ih =>
      have step := (hF k a b ih).pIntegral hs
      rwa [← ha, ← hb, pIntegral_pderiv, pIntegral_pderiv] at step

/-- Formal Picard existence and uniqueness for a causal right-hand side over a
characteristic-zero field. The solution need not define a convergent series. -/
theorem existsUnique_solution [CharZero K] (hF : IsCausal i F) (b : MvPowerSeries σ K) :
    ∃! u : MvPowerSeries σ K, pderiv i u = F u ∧
      ∀ n : σ →₀ ℕ, n i = 0 → coeff n u = coeff n b := by
  classical
  refine ⟨solution i F b, ⟨solution_pde hF, solution_slice⟩, ?_⟩
  intro a ha
  apply formal_unique hF a _ ha.1 (solution_pde hF)
  intro n hn
  exact (ha.2 n (Nat.le_zero.mp hn)).trans (solution_slice n (Nat.le_zero.mp hn)).symm

end Causal
end MvPowerSeries
