/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Coefficients of the almost-IDP simplex polynomial

Multiplying the even geometric sum by the almost-IDP quartic gives a coefficient vector
whose interior repeats the pair $(16,14)$.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Even geometric factor.** For a natural number $n$, the even geometric factor is the
polynomial $\sum_{k=0}^{n-1} z^{2k} = 1 + z^2 + \dots + z^{2n-2}$ with integer coefficients;
for $n = 0$ it is the zero polynomial.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public noncomputable def evenGeometricFactor (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range n, Polynomial.X ^ (2 * k)

/-- **The quartic $1 + 7z + 14z^2 + 7z^3 + z^4$.** The polynomial $1 + 7z + 14z^2 + 7z^3 + z^4$ with
integer coefficients, the quartic factor from Theorem 13.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public noncomputable def almostIDPQuartic : Polynomial ℤ :=
  1 + 7 * Polynomial.X + 14 * Polynomial.X ^ 2 +
    7 * Polynomial.X ^ 3 + Polynomial.X ^ 4

/-- **Coefficient vector $(1, 7, 15, 14, \dots, 15, 7, 1)$.** For a natural number $n$, the list of
integers $(1, 7, 15, 14)$, followed by $n - 2$ copies of the pair $(16, 14)$, followed by
$(15, 7, 1)$. The middle block is empty when $n \le 2$.

It makes exact the ellipsis in the coefficient vector displayed in Theorem 13.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def almostIDPCoefficientVector (n : ℕ) : List ℤ :=
  [1, 7, 15, 14] ++ (List.replicate (n - 2) [16, 14]).flatten ++ [15, 7, 1]

open Polynomial

namespace almostIDP_hStar_coefficients

private theorem evenGeometricFactor_succ (n : ℕ) :
    evenGeometricFactor (n + 1) = evenGeometricFactor n * X ^ 2 + 1 := by
  simp [evenGeometricFactor, Finset.sum_range_succ', Nat.mul_succ, pow_add, Finset.sum_mul]

-- Inserting a pair after the first four coefficients shifts the old product by two
-- degrees and adds one more copy of the quartic at the low end.
private theorem product_eq_ofCoeffList (m : ℕ) :
    evenGeometricFactor (m + 2) * almostIDPQuartic =
      ofCoeffList (almostIDPCoefficientVector (m + 2)) := by
  induction m with
  | zero =>
    norm_num [evenGeometricFactor, Finset.sum_range_succ, almostIDPQuartic,
      almostIDPCoefficientVector, ofCoeffList_cons]
    ring
  | succ m ih =>
    rw [evenGeometricFactor_succ (m + 2), add_mul, one_mul, mul_right_comm, ih]
    simp [almostIDPCoefficientVector, List.replicate_succ, ofCoeffList_cons, almostIDPQuartic]
    ring

end almostIDP_hStar_coefficients

/-- **Coefficients of $(1 + z^2 + \dots + z^{2n-2})(1 + 7z + 14z^2 + 7z^3 + z^4)$.** Let $n \ge 2$.
The coefficients of $z^0, z^1, \dots, z^{2n+2}$ in the integer polynomial
$(1 + z^2 + \dots + z^{2n-2})(1 + 7z + 14z^2 + 7z^3 + z^4)$ are, in order, $1, 7, 15, 14$, then
$n - 2$ repetitions of $16, 14$, then $15, 7, 1$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem almostIDP_hStar_coefficients (n : ℕ) (hn : 2 ≤ n) :
    List.ofFn (fun k : Fin (2 * n + 3) =>
      (evenGeometricFactor n * almostIDPQuartic).coeff k.val) =
      almostIDPCoefficientVector n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [almostIDP_hStar_coefficients.product_eq_ofCoeffList]
  apply List.ext_getElem
  · simp [almostIDPCoefficientVector, List.length_flatten]
    omega
  · intro i hi hj
    simpa only [List.getElem_ofFn, coeff_ofCoeffList] using
      List.getD_eq_getElem _ 0 hj

end

end MetaMathlibExt
