/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import MathlibExt.NumberTheory.Recurrences.CircuitArray
import all MathlibExt.NumberTheory.Recurrences.CircuitArray
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Row one of the multivariable circuit array

The multivariable circuit array replaces the boundary edges by a new variable after each
reduction. We prove the closed form for its first odd row by computing the right edge of a
triangle on the previous reduction's left boundary front.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Variables of the multivariable circuit array.** For a natural number $m$, $X_m$ is the
indeterminate $X_m$ regarded as an element of the field of fractions
$\mathbb{Q}(X_0, X_1, X_2, \dots)$ of the polynomial ring $\mathbb{Q}[X_0, X_1, X_2, \dots]$ in
countably many variables.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 (the variables `X_i`). -/
noncomputable def circuitVar (m : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ)) (MvPolynomial.X m)

/-- **Multivariable circuit array.** Reduce the all-one triangular grid row by row as in Section 2,
and after the $m$-th reduction, for every $m \ge 1$, set every boundary edge (the left edges on the
first diagonal and the right edges on the last diagonal) to the variable $X_m$ of the field of
rational functions over $\mathbb{Q}$ in $X_0, X_1, \dots$. The multivariable circuit array
$C^M_{i,j}$ (Table 3) is the circuit array read off these grids: for $j \ge 1$ and
$0 \le i \le 2(j-1)$, it is the left edge for even $i$, or the right edge for odd $i$, of the
triangle in row $2j - 1$ and diagonal $j - \lfloor (i+1)/2 \rfloor$ of the $j$-times reduced
grid (other indices give junk values). In particular $C^M_{2(m-1),m} = X_m$ for every $m \ge 1$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 and Table 3. -/
noncomputable def circuitArrayM (i j : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  circuitArrayOf (fun m => if m = 0 then none else some (circuitVar m)) i j

/-- **First entries of the left diagonal of the multivariable circuit array.** The multivariable
circuit array $C^M$, with values in the field of rational functions over $\mathbb{Q}$ in the
variables $X_0, X_1, \dots$, satisfies $C^M_{0,1} = X_1$ and $C^M_{2,2} = X_2$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5. -/
theorem circuitArrayM_diagonal :
    circuitArrayM 0 1 = circuitVar 1 ∧ circuitArrayM 2 2 = circuitVar 2 := by
  constructor <;> simp [circuitArrayM, circuitArrayOf, circuitGrid]

namespace circuitArrayM_row_one

/-- **The row-one front value is nonsingular.** For every natural number $k$, the element
$1 - X_1$ of the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$
is not equal to $3 \cdot 9^k$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5. -/
theorem front_nonsingular (k : ℕ) : 1 - circuitVar 1 ≠ 3 * 9 ^ k := by
  intro h
  have hp : 1 - MvPolynomial.X 1 = (3 : MvPolynomial ℕ ℚ) * 9 ^ k := by
    apply IsFractionRing.injective (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
    simpa only [map_sub, map_one, map_mul, map_ofNat, map_pow, circuitVar] using h
  have he := congrArg (MvPolynomial.eval (fun _ => (1 : ℚ))) hp
  simp at he

/-- **Right edge on the left front.** Let $K$ be a field of characteristic zero and let
$x, q \in K$ with $q \ne 0$ and $x + 3q - 1 \ne 0$. Then the wye-delta value
`circuitY` of the delta-wye values $\Delta(1, 1, 1)$, $\Delta(1, 1, 1 - (1 - x)/q)$ and
$\Delta(1, 1, 1)$ is $(9q - 1 + x)/(3(x + 3q - 1))$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 2 and the proof of Corollary 4.10. -/
theorem rightEdge_value {K : Type*} [Field K] [CharZero K] (x q : K)
    (hq : q ≠ 0) (hd : x + 3 * q - 1 ≠ 0) :
    circuitY (circuitDelta 1 1 1) (circuitDelta 1 1 (1 - (1 - x) / q)) (circuitDelta 1 1 1) =
      (9 * q - 1 + x) / (3 * (x + 3 * q - 1)) := by
  have hsum : 1 + 1 + (1 - (1 - x) / q) = (x + 3 * q - 1) / q := by
    field_simp
    ring
  rw [circuitY, circuitDelta, circuitDelta, hsum]
  field_simp
  ring

end circuitArrayM_row_one

open circuitArrayM_row_one

/-- **Row 1 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 2$,
$C^M_{1,s} = (9^{s-1} - 1 + X_1)/\bigl(3(X_1 + 3 \cdot 9^{s-2} - 1)\bigr)$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.10 (`fq-2024-hendel08232024rev2-cor-4.10`). -/
theorem circuitArrayM_row_one (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayM 1 s =
      (9 ^ (s - 1) - 1 + circuitVar 1) / (3 * (circuitVar 1 + 3 * 9 ^ (s - 2) - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  let bdry (m : ℕ) := if m = 0 then none else some (circuitVar m)
  set r := 2 * k + 3 with hr
  have hstart : (bdry 1).getD (2 / 3) = 1 - (1 - circuitVar 1) := by simp [bdry]
  have hfront := circuitGrid_front bdry (1 - circuitVar 1) hstart front_nonsingular k r (by omega)
  obtain ⟨_, hR, hB⟩ := circuitGrid_eq_one bdry (k + 1)
  -- On diagonal k + 1 the left edge has the front value and the other two edges are 1.
  -- Both neighboring triangles on diagonal k + 2 still have all three edges equal to 1.
  change circuitArrayOf bdry 1 (k + 2) = _
  rw [circuitArrayOf, show 2 * (k + 2) - 1 = r by omega,
    show k + 2 - (1 + 1) / 2 = k + 1 by omega, ite_eq_right (by decide),
    circuitGrid_succ_right bdry (k + 1) r (k + 1) (by omega),
    circuitGrid_eq_one_fun bdry (k + 1) r (k + 1 + 1) (by omega) (by omega),
    circuitGrid_eq_one_fun bdry (k + 1) (r + 1) (k + 1 + 1) (by omega) (by omega)]
  simp only [circuitRightEdge, circuitLeftArm, circuitRightArm, circuitTopArm]
  rw [hR r (k + 1) le_rfl (by omega), hB r (k + 1) le_rfl (by omega), hfront,
    Nat.add_sub_cancel, pow_succ']
  apply rightEdge_value _ _ (pow_ne_zero _ (by norm_num))
  intro h
  apply front_nonsingular k
  linear_combination -h

end

end MetaMathlibExt
