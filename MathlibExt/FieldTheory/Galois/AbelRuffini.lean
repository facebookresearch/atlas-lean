/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abel–Ruffini theorem

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
the `abel_ruffini` statement below is taken verbatim from
leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e,
module `LeanEval.Algebra.AbelRuffini` (manifest
`manifests/problems/abel_ruffini.toml`, statement revision 1, submitter
Kim Morrison), which is distributed under the Apache License, Version 2.0.
The original statement had no per-file copyright header and lean-eval
ships no `NOTICE` file. Changes made in this file: converted the original
`@[eval_problem] theorem … := by sorry` into a Batteries
`theorem_wanted`, replaced `import Mathlib` and `EvalTools.Markers` with
minimal imports, placed the declaration in the
`MathlibExt.Algebra.AbelRuffiniWanted` namespace, and corrected the
source docstring's reversed forward/reverse direction descriptions. The
mathematical statement itself is unchanged.
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.AbelRuffini
import Archive.Wiedijk100Theorems.AbelRuffini
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Abel–Ruffini theorem

We prove radical solvability for every root in degrees one through four, using the
quadratic formula and the reductions of Cardano and Ferrari. For the other direction
we use the nonsolvable quintic from Mathlib's Archive and multiply it by a power of `X`.
-/

namespace MathlibExt.Algebra.AbelRuffiniWanted

open Polynomial
open scoped BigOperators

local notation "S" => solvableByRad ℚ ℂ

private theorem nat_mem (n : ℕ) : (n : ℂ) ∈ S := by
  exact IntermediateField.natCast_mem S n

private theorem quadratic {t B C : ℂ} (hB : B ∈ S) (hC : C ∈ S)
    (h : t ^ 2 + B * t + C = 0) : t ∈ S := by
  have hsq : (2 * t + B) ^ 2 = B ^ 2 - 4 * C := by
    linear_combination 4 * h
  have hrad : 2 * t + B ∈ S :=
    solvableByRad.rad_mem (n := 2) (by decide)
      (hsq ▸ sub_mem (pow_mem hB 2) (mul_mem (nat_mem 4) hC))
  have heq : t = (2 * t + B - B) / 2 := by ring
  rw [heq]
  exact div_mem (sub_mem hrad hB) (nat_mem 2)

-- Recover the two summands from the given root, rather than choosing compatible cube roots.
private theorem depressedCubic {t P Q : ℂ} (hP : P ∈ S) (hQ : Q ∈ S)
    (h : t ^ 3 + P * t + Q = 0) : t ∈ S := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((t / 2) ^ 2 + P / 3)
    (n := 2) (by decide)
  let u := t / 2 + s
  let v := t / 2 - s
  have huv : u * v = -P / 3 := by
    dsimp [u, v]
    linear_combination -hs
  have hsum : u ^ 3 + v ^ 3 = -Q := by
    dsimp [u, v]
    linear_combination h + 3 * t * hs
  have hprod : u ^ 3 * v ^ 3 = (-P / 3) ^ 3 := by rw [← mul_pow, huv]
  have hconst : (-P / 3) ^ 3 ∈ S := pow_mem (div_mem (neg_mem hP) (nat_mem 3)) 3
  have hu : u ∈ S := by
    apply solvableByRad.rad_mem (n := 3) (by decide)
    exact quadratic hQ hconst (by linear_combination u ^ 3 * hsum - hprod)
  have hv : v ∈ S := by
    apply solvableByRad.rad_mem (n := 3) (by decide)
    exact quadratic hQ hconst (by linear_combination v ^ 3 * hsum - hprod)
  have heq : t = u + v := by dsimp [u, v]; ring
  rw [heq]
  exact add_mem hu hv

private theorem cubic {x A B C : ℂ} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (h : x ^ 3 + A * x ^ 2 + B * x + C = 0) : x ∈ S := by
  let a := A / 3
  let t := x + a
  have ha : a ∈ S := div_mem hA (nat_mem 3)
  have ht : t ^ 3 + (B - 3 * a ^ 2) * t + (2 * a ^ 3 - a * B + C) = 0 := by
    dsimp [t, a]
    linear_combination h
  have ht' := depressedCubic (sub_mem hB (mul_mem (nat_mem 3) (pow_mem ha 2)))
    (add_mem (sub_mem (mul_mem (nat_mem 2) (pow_mem ha 3)) (mul_mem ha hB)) hC) ht
  exact (add_sub_cancel_right x a) ▸ sub_mem ht' ha

private theorem depressedQuartic {t P Q R : ℂ} (hP : P ∈ S) (hQ : Q ∈ S) (hR : R ∈ S)
    (h : t ^ 4 + P * t ^ 2 + Q * t + R = 0) : t ∈ S := by
  by_cases hQ0 : Q = 0
  · apply solvableByRad.rad_mem (n := 2) (by decide)
    exact quadratic hP hR (by linear_combination h - t * hQ0)
  -- The resolvent yields a nonzero square `m = s²` for the linear coefficients.
  let f : ℂ[X] := X ^ 3 + C (2 * P) * X ^ 2 + C (P ^ 2 - 4 * R) * X + C (-Q ^ 2)
  have hf : f.degree = 3 := by
    simpa only [f, C_1, one_mul] using
      (degree_cubic (d := -Q ^ 2) (c := P ^ 2 - 4 * R) (b := 2 * P) (one_ne_zero : (1 : ℂ) ≠ 0))
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_root f (by rw [hf]; decide)
  have hm : m ^ 3 + (2 * P) * m ^ 2 + (P ^ 2 - 4 * R) * m - Q ^ 2 = 0 := by
    simpa only [IsRoot, f, eval_add, eval_mul, eval_C, eval_X_pow, eval_X, sub_eq_add_neg] using hm
  have hmS : m ∈ S := cubic (mul_mem (nat_mem 2) hP)
    (sub_mem (pow_mem hP 2) (mul_mem (nat_mem 4) hR)) (neg_mem (pow_mem hQ 2))
    (by simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hm)
  have hm0 : m ≠ 0 := by
    intro hm0
    simp [hm0, hQ0] at hm
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq m (n := 2) (by decide)
  have hsS : s ∈ S := solvableByRad.rad_mem (n := 2) (by decide) (hs ▸ hmS)
  have hs0 : s ≠ 0 := by
    intro hs0
    exact hm0 (by simpa [hs0] using hs.symm)
  let d := Q / s
  have hd : s * d = Q := by rw [mul_comm, show d = Q / s from rfl, div_mul_cancel₀ _ hs0]
  have hdS : d ∈ S := div_mem hQ hsS
  let bMinus := (P + m - d) / 2
  let bPlus := (P + m + d) / 2
  have hbMinus : bMinus ∈ S := div_mem (sub_mem (add_mem hP hmS) hdS) (nat_mem 2)
  have hbPlus : bPlus ∈ S := div_mem (add_mem (add_mem hP hmS) hdS) (nat_mem 2)
  have hsum : bMinus + bPlus = P + m := by dsimp [bMinus, bPlus]; ring
  have hsub : bPlus - bMinus = d := by dsimp [bMinus, bPlus]; ring
  have hm' : m * ((P + m) ^ 2 - 4 * R) = Q ^ 2 := by linear_combination hm
  have hd' : m * d ^ 2 = Q ^ 2 := by rw [← hs, ← mul_pow, hd]
  have hdiff : (P + m) ^ 2 - 4 * R - d ^ 2 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hm0
    linear_combination hm' - hd'
  have hprod : bMinus * bPlus = R := by
    dsimp [bMinus, bPlus]
    linear_combination (1 / 4 : ℂ) * hdiff
  have hfactor : (t ^ 2 + s * t + bMinus) * (t ^ 2 - s * t + bPlus) = 0 := by
    calc
      _ = t ^ 4 + (bMinus + bPlus - s ^ 2) * t ^ 2 + s * (bPlus - bMinus) * t +
          bMinus * bPlus := by ring
      _ = 0 := by simpa [hsum, hsub, hs, hd, hprod] using h
  rcases mul_eq_zero.mp hfactor with hLeft | hRight
  · exact quadratic hsS hbMinus hLeft
  · exact quadratic (neg_mem hsS) hbPlus (by simpa [sub_eq_add_neg] using hRight)

private theorem quartic {x A B C D : ℂ} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (hD : D ∈ S) (h : x ^ 4 + A * x ^ 3 + B * x ^ 2 + C * x + D = 0) : x ∈ S := by
  let a := A / 4
  let t := x + a
  have ha : a ∈ S := div_mem hA (nat_mem 4)
  have ht : t ^ 4 + (B - 6 * a ^ 2) * t ^ 2 + (C - 2 * a * B + 8 * a ^ 3) * t +
      (D - a * C + a ^ 2 * B - 3 * a ^ 4) = 0 := by
    dsimp [t, a]
    linear_combination h
  have ht' := depressedQuartic (sub_mem hB (mul_mem (nat_mem 6) (pow_mem ha 2)))
    (add_mem (sub_mem hC (mul_mem (mul_mem (nat_mem 2) ha) hB))
      (mul_mem (nat_mem 8) (pow_mem ha 3)))
    (sub_mem (add_mem (sub_mem hD (mul_mem ha hC)) (mul_mem (pow_mem ha 2) hB))
      (mul_mem (nat_mem 3) (pow_mem ha 4))) ht
  exact (add_sub_cancel_right x a) ▸ sub_mem ht' ha

private theorem smallDegree {n : ℕ} (hn : 1 ≤ n) (hn₄ : n ≤ 4) {p : ℚ[X]}
    (hp : p.natDegree = n) {x : ℂ} (hx : aeval x p = 0) : x ∈ S := by
  let a (i : ℕ) : ℂ := algebraMap ℚ ℂ (p.coeff i / p.leadingCoeff)
  have ha (i : ℕ) : a i ∈ S := IntermediateField.algebraMap_mem S _
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hp
    omega
  have htop : a n = 1 := by
    dsimp [a]
    rw [← hp, coeff_natDegree, div_self (leadingCoeff_ne_zero.mpr hp0), map_one]
  have heval : ∑ i ∈ Finset.range (n + 1), x ^ i * algebraMap ℚ ℂ (p.coeff i) = 0 := by
    simpa only [Polynomial.aeval_eq_sum_range, hp, Algebra.smul_def, mul_comm] using hx
  have hmonic : ∑ i ∈ Finset.range (n + 1), x ^ i * a i = 0 := by
    simp only [a, map_div₀, ← mul_div_assoc, ← Finset.sum_div, heval, zero_div]
  rw [Finset.sum_range_succ, htop, mul_one, add_comm] at hmonic
  interval_cases n
  · have h' : x = -a 0 := by simpa [Finset.sum_range_succ, eq_neg_iff_add_eq_zero] using hmonic
    rw [h']
    exact neg_mem (ha 0)
  · exact quadratic (ha 1) (ha 0) (by
      simpa [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm, mul_comm] using hmonic)
  · exact cubic (ha 2) (ha 1) (ha 0) (by
      simpa [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm, mul_comm] using hmonic)
  · exact quartic (ha 3) (ha 2) (ha 1) (ha 0) (by
      simpa [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm, mul_comm] using hmonic)

private theorem highDegree {n : ℕ} (hn : 5 ≤ n) :
    ∃ p : ℚ[X], p.natDegree = n ∧ ∃ x : ℂ, aeval x p = 0 ∧ x ∉ S := by
  let q := AbelRuffini.Φ ℚ 4 2
  have hq : q.natDegree = 5 := AbelRuffini.natDegree_Phi 4 2
  have hq0 : q ≠ 0 := (AbelRuffini.monic_Phi 4 2).ne_zero
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ q
    (by rw [show q.degree = 5 from AbelRuffini.degree_Phi 4 2]; decide)
  refine ⟨q * X ^ (n - 5), ?_, x, ?_, AbelRuffini.not_solvable_by_rad' x hx⟩
  · rw [natDegree_mul_X_pow _ hq0, hq]
    omega
  · simp [hx]

/--
**Abel–Ruffini theorem.** Let $n \ge 1$ be a natural number. Every complex root of every
polynomial with rational coefficients of degree exactly $n$ is expressible by radicals over
$\mathbb{Q}$ if and only if $n \le 4$. Here a complex number is expressible by radicals over
$\mathbb{Q}$ when it lies in the smallest subfield $S$ of $\mathbb{C}$ such that $z \in S$
whenever $z \in \mathbb{C}$ and $z^k \in S$ for some integer $k \ge 1$.

The direction from radical solvability to $n \le 4$ is the classical insolvability of the
general quintic, extended to higher degrees; the converse follows from the explicit formulas
of Cardano and Ferrari for degrees at most four.

Source: P. Ruffini (1799), N. H. Abel (1824), É. Galois (1832). Listed as §57
in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf);
the general-quintic insolvability is #16 on Freek Wiedijk's *Formalizing 100
Theorems* list (https://www.cs.ru.nl/~freek/100/). Taken verbatim, with no
Lean variant, from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, manifest
`manifests/problems/abel_ruffini.toml` (statement revision 1), module
`LeanEval.Algebra.AbelRuffini`, hole `abel_ruffini`.
-/
public theorem abel_ruffini (n : ℕ) (_hn : 1 ≤ n) :
    (∀ p : ℚ[X], p.natDegree = n → ∀ x : ℂ, aeval x p = 0 →
        x ∈ solvableByRad ℚ ℂ) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra! hn
    obtain ⟨p, hp, x, hx, hxS⟩ := highDegree (n := n) hn
    exact hxS (h p hp x hx)
  · intro hn p hp x hx
    exact smallDegree _hn hn hp hx

end MathlibExt.Algebra.AbelRuffiniWanted
