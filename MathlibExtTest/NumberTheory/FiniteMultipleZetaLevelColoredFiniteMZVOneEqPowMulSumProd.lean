/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FiniteMultipleZetaLevelColoredFiniteMZVOneEqPowMulSumProd
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Tests for decomposition of finite multiple zeta values

Concrete consequences of the decomposition for an empty index and an index of weight zero.

Source: Shin-ichiro Seki, *Regular Primes, Non-Wieferich Primes, and Finite
Multiple Zeta Values of Level N*, INTEGERS 24 (2024), Article A22 (arXiv:2310.06809).
-/

namespace MathlibExtTest.NumberTheory.FiniteMultipleZetaLevelColoredFiniteMZVOneEqPowMulSumProd

open Filter MetaMathlibExt

private lemma empty (p N : ℕ) (k : Fin 0 → ℕ) (a : Fin 0 → ZMod N) :
    coloredFiniteMZV p N k a = 1 := by
  classical
  rw [coloredFiniteMZV, Finset.filter_true_of_mem fun m _ =>
    ⟨fun u => Fin.elim0 u, fun t => Fin.elim0 t⟩]
  simp

private lemma mono_one {r : ℕ} (i : Fin 1 → Fin r) : Monotone i := by
  intro a b _
  have h : a = b := Subsingleton.elim _ _
  subst b
  rfl

private lemma sum_one (r p : ℕ) (f : (Fin 1 → Fin r) → ZMod p) :
    (∑ i, f i) = ∑ a : Fin r, f (fun _ => a) := by
  apply Fintype.sum_equiv (Equiv.piUnique (fun _ : Fin 1 => Fin r))
  intro i
  congr 1
  funext t
  exact congrArg i (Subsingleton.elim _ _)

private lemma zero_depth_congr (p N r s : ℕ) (h : r = s) (a : ZMod N) :
    coloredFiniteMZV p N (fun _ : Fin r => 0) (fun _ => a) =
      coloredFiniteMZV p N (fun _ : Fin s => 0) (fun _ => a) := by
  subst s
  rfl

private lemma singleton_piece (p N : ℕ) (a : ZMod N) :
    coloredFiniteMZV p N
      (fun _ : Fin ((([0] : List ℕ).drop 0).take 1).length => 0) (fun _ => a) =
        coloredFiniteMZV p N (fun _ : Fin 1 => 0) (fun _ => a) := by
  apply zero_depth_congr
  simp

example : ∀ᶠ p in atTop, p.Prime →
    coloredFiniteMZV p 1 (fun t : Fin 0 => ([] : List ℕ).get t) 0 =
      coloredFiniteMZV p 2 (fun t : Fin 0 => ([] : List ℕ).get t) 0 *
        coloredFiniteMZV p 2 (fun t : Fin 0 => ([] : List ℕ).get t)
          (fun _ => -(p : ZMod 2)) := by
  simpa [mono_one, Fin.prod_univ_two, Pi.zero_def] using
    coloredFiniteMZV_one_eq_pow_mul_sum_prod (N := 2) (by decide) []

example : ∀ᶠ p in atTop, p.Prime →
    coloredFiniteMZV p 1 (fun _ : Fin 1 => 0) 0 =
      coloredFiniteMZV p 2 (fun _ : Fin 1 => 0) 0 +
        coloredFiniteMZV p 2 (fun _ : Fin 1 => 0) (fun _ => -(p : ZMod 2)) := by
  have h := coloredFiniteMZV_one_eq_pow_mul_sum_prod (N := 2) (by decide) [0]
  simpa [mono_one, sum_one, Fin.prod_univ_two, Fin.sum_univ_two, empty, Pi.zero_def,
    singleton_piece, add_comm] using h

end MathlibExtTest.NumberTheory.FiniteMultipleZetaLevelColoredFiniteMZVOneEqPowMulSumProd
