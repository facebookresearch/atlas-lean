/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Ring.Finset
import MathlibExt.Combinatorics.Enumerative.HypersequenceBinomial

/-!
# Closed form for hyperlucas numbers

For positive generations, the reversed binomial expansion of a hypersequence identifies the
first sum in the shifted Lucas-number identity. Subtracting the correction sum gives the closed
form over the integers.

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
  INTEGERS 24 (2024), Article A70, pp. 1–31, Theorems 1 and 5 and Corollary 2.
  <https://math.colgate.edu/~integers/y70/y70.pdf>
-/

namespace MetaMathlibExt

open Finset

/-- **Hyperlucas numbers in terms of Lucas numbers.** Let $L_n$ denote the Lucas numbers and
let $L^{(r)}_n$ denote the hyperlucas numbers, the hypersequence of generation $r$ of $(L_n)$.
For all natural numbers $r$ and $n$, in the integers,
$$L^{(r)}_n = L_{n+2r} - \sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 5, Equation (2.12) (`integers-2024-A70-thm-5`). -/
public theorem hyperLucas_eq_lucas_sub_sum (r n : ℕ) :
    ((hypersequence lucasNumber r n : ℕ) : ℤ) =
      lucasNumber (n + 2 * r) -
        ∑ k ∈ range r, ((n + k).choose k * lucasNumber (2 * (r - k) - 1) : ℕ) := by
  by_cases hr : r = 0
  · subst r
    simp [hypersequence]
  have hpos : 1 ≤ r := Nat.pos_of_ne_zero hr
  have hcast (s m : ℕ) : hypersequence (fun k ↦ (lucasNumber k : ℂ)) s m =
      ((hypersequence lucasNumber s m : ℕ) : ℂ) := by
    induction s generalizing m with
    | zero => rfl
    | succ s ih => simp only [hypersequence_succ, Nat.cast_sum, ih]
  have hsum := (hypersequence_eq_sum_choose (fun k ↦ (lucasNumber k : ℂ)) hpos n).2
  rw [hcast] at hsum
  have hsumNat : hypersequence lucasNumber r n =
      ∑ k ∈ range (n + 1), (r + k - 1).choose k * lucasNumber (n - k) := by
    exact_mod_cast hsum
  have h := (lucas_add_two_mul_eq_sum_choose hpos n).2
  rw [← hsumNat] at h
  apply eq_sub_of_add_eq
  exact_mod_cast h.symm

end MetaMathlibExt
