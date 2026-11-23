/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/ODE/DirichletEigenvalues.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `dirichlet_eigenvalues_eq_nat_sq`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/dirichlet_eigenvalues_eq_nat_sq.toml`, rev 1, submitter Kim Morrison, status
archived): the statement of `dirichlet_eigenvalues_eq_nat_sq`, with the docstring and comments it
had in the former wanted module `WantedExt/Analysis/DirichletEigenvaluesWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Analysis.DirichletEigenvaluesWanted` namespace. Mathematical statements are unchanged.
Later changes (ATLAS, 2026): the docstring of `dirichlet_eigenvalues_eq_nat_sq` was restated to
match the Lean statement; then the `theorem_wanted` was proved and moved from
`WantedExt/Analysis/DirichletEigenvaluesWanted.lean` to this `MathlibExt` module with unchanged
name, statement and docstring, and the import of `Batteries.Util.ProofWanted` was dropped.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`dirichlet_eigenvalues_eq_nat_sq`, the private lemmas it uses, the module documentation and the
linter option.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Dirichlet eigenvalues of `-y'' = λ y` on `[0, π]`

`dirichlet_eigenvalues_eq_nat_sq`: for a real number `λ`, there is a function `y`, twice
differentiable on an open set `J ⊇ [0, π]` with `y'' = -λ y` on `J`, `y 0 = y π = 0` and `y` not
identically zero on `(0, π)`, if and only if `λ = n ^ 2` for a positive natural number `n`.

## Proof outline

* If `λ = n ^ 2` with `n > 0`, then `y x = sin (n x)` on `J = ℝ` works: it vanishes at `0` and
  at `π`, and it equals `1` at `π / (2 n) ∈ (0, π)`.
* Conversely, take solutions `c` and `s` of `u'' = -λ u` on `ℝ` with `c 0 = 1`, `c' 0 = 0`,
  `s 0 = 0`, `s' 0 = 1` and Wronskian `c s' - c' s = 1`: `cos (k x)` and `sin (k x) / k` with
  `k = √λ` if `λ > 0`, `1` and `x` if `λ = 0`, and `cosh (k x)` and `sinh (k x) / k` with
  `k = √(-λ)` if `λ < 0`. The Wronskians `y s' - y' s` and `y c' - y' c` have zero derivative on
  `J`, so they are constant on `[0, π]`, and eliminating `y'` gives `y = y 0 · c + y' 0 · s` on
  `[0, π]`. As `y 0 = 0` and `y` does not vanish identically on `(0, π)`, `y' 0 ≠ 0`, so `y π = 0`
  forces `s π = 0`. This rules out `s π = π` and `s π = sinh (k π) / k > 0`, and
  `sin (k π) / k = 0` means that `k` is an integer, positive since `k > 0`, with `λ = k ^ 2`.

## Implementation notes

The statement keeps the full name it had in the former wanted module, so the namespace still reads
`DirichletEigenvaluesWanted` and repeats `Analysis`; the `dupNamespace` linter is turned off for
this declaration only.

## References

* Classical Sturm–Liouville theory. This is the source cited by problem
  `dirichlet_eigenvalues_eq_nat_sq` of the lean-eval benchmark (leanprover/lean-eval), from which
  the statement is taken.
-/

@[expose] public section

namespace MathlibExt.Analysis.DirichletEigenvaluesWanted
namespace Analysis
namespace ODE

open scoped Real

/-!
Dirichlet eigenvalues of `-y'' = λ y` on `[0, π]`.

A nontrivial `C²` solution `y` (defined on some open interval `J` containing `[0, π]`)
of `-y''(x) = λ y(x)` with `y 0 = y π = 0` exists **iff** `λ = n²` for some positive
natural number `n`.

The "if" direction is straightforward (`sin (n · x)` works). The "only if" direction is
the substantive content: it requires casing on the sign of `λ` and ruling out `λ < 0`
(only the zero solution; uses `sinh`/`cosh` linear independence) and `λ = 0` (only the
zero solution), and for `λ > 0` showing that `√λ` must be a positive integer.
-/

open Set

/-- A function with zero derivative at every point of a set containing `[a, b]` is constant on
`[a, b]`. -/
private lemma eq_left_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ} {J : Set ℝ} (hJ : Icc a b ⊆ J)
    (hf : ∀ x ∈ J, HasDerivAt f 0 x) : ∀ x ∈ Icc a b, f x = f a :=
  constant_of_has_deriv_right_zero (fun x hx => (hf x (hJ hx)).continuousAt.continuousWithinAt)
    fun x hx => (hf x (hJ (Ico_subset_Icc_self hx))).hasDerivWithinAt

/-- Let `c` and `s` be solutions of `u'' = -λ u` on `ℝ`, with derivatives `c'` and `s'`, such that
`c 0 = 1`, `c' 0 = 0`, `s 0 = 0`, `s' 0 = 1` and `c s' - c' s = 1`. Then every solution `y` of
`y'' = -λ y` on a set containing `[0, π]` equals `y 0 · c + y' 0 · s` on `[0, π]`. -/
private lemma eq_of_fundamental {lam : ℝ} {y c c' s s' : ℝ → ℝ} {J : Set ℝ}
    (hJ : Icc 0 π ⊆ J) (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy' : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hc : ∀ x, HasDerivAt c (c' x) x) (hc' : ∀ x, HasDerivAt c' (-(lam * c x)) x)
    (hs : ∀ x, HasDerivAt s (s' x) x) (hs' : ∀ x, HasDerivAt s' (-(lam * s x)) x)
    (hc0 : c 0 = 1) (hc'0 : c' 0 = 0) (hs0 : s 0 = 0) (hs'0 : s' 0 = 1)
    (hW : ∀ x, c x * s' x - c' x * s x = 1) {x : ℝ} (hx : x ∈ Icc 0 π) :
    y x = y 0 * c x + deriv y 0 * s x := by
  -- the Wronskians of `y` with `s` and with `c` are constant on `[0, π]`
  have e₁ := eq_left_of_hasDerivAt_zero hJ (f := fun x => y x * s' x - deriv y x * s x)
    (fun t ht => (((hy t ht).mul (hs' t)).sub ((hy' t ht).mul (hs t))).congr_deriv (by ring)) x hx
  have e₂ := eq_left_of_hasDerivAt_zero hJ (f := fun x => y x * c' x - deriv y x * c x)
    (fun t ht => (((hy t ht).mul (hc' t)).sub ((hy' t ht).mul (hc t))).congr_deriv (by ring)) x hx
  simp only [hc0, hc'0, hs0, hs'0, mul_one, mul_zero, sub_zero, zero_sub] at e₁ e₂
  linear_combination c x * e₁ - s x * e₂ - y x * hW x

/-- With `c` and `s` as in `eq_of_fundamental`, a solution `y` of `y'' = -λ y` on a set containing
`[0, π]` that vanishes at `0` and at `π` but not everywhere on `(0, π)` forces `s π = 0`. -/
private lemma snd_pi_eq_zero {lam : ℝ} {y c c' s s' : ℝ → ℝ} {J : Set ℝ}
    (hJ : Icc 0 π ⊆ J) (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy' : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) (hy0 : y 0 = 0) (hyπ : y π = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo 0 π) (hyx₀ : y x₀ ≠ 0)
    (hc : ∀ x, HasDerivAt c (c' x) x) (hc' : ∀ x, HasDerivAt c' (-(lam * c x)) x)
    (hs : ∀ x, HasDerivAt s (s' x) x) (hs' : ∀ x, HasDerivAt s' (-(lam * s x)) x)
    (hc0 : c 0 = 1) (hc'0 : c' 0 = 0) (hs0 : s 0 = 0) (hs'0 : s' 0 = 1)
    (hW : ∀ x, c x * s' x - c' x * s x = 1) : s π = 0 := by
  have key : ∀ x ∈ Icc 0 π, y x = deriv y 0 * s x := fun x hx => by
    rw [eq_of_fundamental hJ hy hy' hc hc' hs hs' hc0 hc'0 hs0 hs'0 hW hx, hy0, zero_mul,
      zero_add]
  have hd : deriv y 0 ≠ 0 := fun h => hyx₀ (by rw [key x₀ (Ioo_subset_Icc_self hx₀), h, zero_mul])
  have hπ := key π (right_mem_Icc.2 Real.pi_pos.le)
  rw [hyπ] at hπ
  exact (mul_eq_zero.1 hπ.symm).resolve_left hd

/- **Dirichlet eigenvalue characterization.** A real `λ` is a Dirichlet eigenvalue of
`-y'' = λ y` on `[0, π]` (i.e. there is a nontrivial `C²` solution on some open interval
containing `[0, π]`, vanishing at both endpoints) iff `λ = n²` for some positive natural
number `n`. -/
set_option linter.dupNamespace false in
/-- **Dirichlet eigenvalues of $-y'' = \lambda y$ on $[0, \pi]$.** For every real number
$\lambda$, the following are equivalent:
(i) there are a function $y : \mathbb{R} \to \mathbb{R}$ and an open set $J \subseteq \mathbb{R}$
containing $[0, \pi]$ such that $y$ is differentiable at every point of $J$, its derivative $y'$
is differentiable at every $x \in J$ with $y''(x) = -\lambda y(x)$, $y(0) = y(\pi) = 0$, and
$y(x) \ne 0$ for some $x \in (0, \pi)$;
(ii) $\lambda = n^2$ for some positive integer $n$.

Source: Classical Sturm-Liouville theory. Via leanprover/lean-eval@38361be, problem
`dirichlet_eigenvalues_eq_nat_sq`. -/
theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  constructor
  · rintro ⟨y, J, -, hJ, hy, hy', hy0, hyπ, x₀, hx₀, hyx₀⟩
    rcases lt_trichotomy lam 0 with hlam | rfl | hlam
    · -- `λ < 0`: the fundamental pair `cosh (k x)`, `sinh (k x) / k` with `k = √(-λ)`
      exfalso
      obtain ⟨k, hk, hk2⟩ : ∃ k : ℝ, 0 < k ∧ k ^ 2 = -lam :=
        ⟨√(-lam), Real.sqrt_pos.2 (neg_pos.2 hlam), Real.sq_sqrt (neg_nonneg.2 hlam.le)⟩
      have hk0 : k ≠ 0 := hk.ne'
      have hsπ := snd_pi_eq_zero hJ hy hy' hy0 hyπ hx₀ hyx₀
        (c := fun x => Real.cosh (k * x)) (c' := fun x => k * Real.sinh (k * x))
        (s := fun x => Real.sinh (k * x) / k) (s' := fun x => Real.cosh (k * x))
        (fun x => (hasDerivAt_const_mul (x := x) k).cosh.congr_deriv (by ring))
        (fun x => ((hasDerivAt_const_mul (x := x) k).sinh.const_mul k).congr_deriv
          (by linear_combination Real.cosh (k * x) * hk2))
        (fun x => ((hasDerivAt_const_mul (x := x) k).sinh.div_const k).congr_deriv
          (by field_simp))
        (fun x => (hasDerivAt_const_mul (x := x) k).cosh.congr_deriv
          (by field_simp; linear_combination Real.sinh (k * x) * hk2))
        (by simp) (by simp) (by simp) (by simp)
        (fun x => by field_simp; linear_combination Real.cosh_sq_sub_sinh_sq (k * x))
      exact (div_pos (Real.sinh_pos_iff.2 (mul_pos hk Real.pi_pos)) hk).ne' hsπ
    · -- `λ = 0`: the fundamental pair `1`, `x`
      exfalso
      have hsπ := snd_pi_eq_zero hJ hy hy' hy0 hyπ hx₀ hyx₀
        (c := fun _ => 1) (c' := fun _ => 0) (s := fun x => x) (s' := fun _ => 1)
        (fun x => (hasDerivAt_const x 1).congr_deriv (by ring))
        (fun x => (hasDerivAt_const x 0).congr_deriv (by ring))
        (fun x => hasDerivAt_id' x)
        (fun x => (hasDerivAt_const x 1).congr_deriv (by ring))
        rfl rfl rfl rfl (fun x => by ring)
      exact Real.pi_ne_zero hsπ
    · -- `λ > 0`: the fundamental pair `cos (k x)`, `sin (k x) / k` with `k = √λ`
      obtain ⟨k, hk, hk2⟩ : ∃ k : ℝ, 0 < k ∧ k ^ 2 = lam :=
        ⟨√lam, Real.sqrt_pos.2 hlam, Real.sq_sqrt hlam.le⟩
      have hk0 : k ≠ 0 := hk.ne'
      have hsπ := snd_pi_eq_zero hJ hy hy' hy0 hyπ hx₀ hyx₀
        (c := fun x => Real.cos (k * x)) (c' := fun x => -(k * Real.sin (k * x)))
        (s := fun x => Real.sin (k * x) / k) (s' := fun x => Real.cos (k * x))
        (fun x => (hasDerivAt_const_mul (x := x) k).cos.congr_deriv (by ring))
        (fun x => ((hasDerivAt_const_mul (x := x) k).sin.const_mul k).neg.congr_deriv
          (by linear_combination -Real.cos (k * x) * hk2))
        (fun x => ((hasDerivAt_const_mul (x := x) k).sin.div_const k).congr_deriv
          (by field_simp))
        (fun x => (hasDerivAt_const_mul (x := x) k).cos.congr_deriv
          (by field_simp; linear_combination -Real.sin (k * x) * hk2))
        (by simp) (by simp) (by simp) (by simp)
        (fun x => by field_simp; linear_combination Real.sin_sq_add_cos_sq (k * x))
      obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 ((div_eq_zero_iff.1 hsπ).resolve_right hk0)
      have hmk : (m : ℝ) = k := mul_right_cancel₀ Real.pi_ne_zero hm
      have hm0 : 0 < m := by exact_mod_cast hmk ▸ hk
      lift m to ℕ using hm0.le
      refine ⟨m, by exact_mod_cast hm0, ?_⟩
      rw [← hk2, ← hmk]
      norm_cast
  · rintro ⟨n, hn, rfl⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hd : ∀ x, HasDerivAt (fun x => Real.sin (n * x)) (Real.cos (n * x) * n) x := fun x =>
      (hasDerivAt_const_mul (x := x) (n : ℝ)).sin
    have hderiv : deriv (fun x => Real.sin (n * x)) = fun x => Real.cos (n * x) * n :=
      funext fun x => (hd x).deriv
    refine ⟨fun x => Real.sin (n * x), univ, isOpen_univ, subset_univ _, fun x _ => ?_,
      fun x _ => ?_, by simp, Real.sin_nat_mul_pi n, π / (2 * n), ⟨by positivity, ?_⟩, ?_⟩
    · rw [hderiv]
      exact hd x
    · rw [hderiv]
      exact ((hasDerivAt_const_mul (x := x) (n : ℝ)).cos.mul_const (n : ℝ)).congr_deriv (by ring)
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, (show (1 : ℝ) ≤ n by exact_mod_cast hn)]
    · dsimp only
      rw [show (n : ℝ) * (π / (2 * n)) = π / 2 by field_simp, Real.sin_pi_div_two]
      exact one_ne_zero

end ODE
end Analysis

end MathlibExt.Analysis.DirichletEigenvaluesWanted
