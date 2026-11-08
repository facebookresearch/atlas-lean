/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- `p_{1,ℓ}(n)`: the number of 2-color partitions of `n` in which the parts of the second
color are multiples of `ℓ`, i.e. for `0 < ℓ` the coefficient of `qⁿ` in `1/(f₁ f_ℓ)` with
`f_m = ∏_{j ≥ 1} (1 - q^{mj})`; computed as `∑_{j ≤ n/ℓ} p(n - ℓj) p(j)`. For `ℓ = 0` there is
no generating-function reading (`f₀` vanishes); Lean's `n / 0 = 0` makes the value `p(n)`, a
convention only. The paper uses `ℓ = 7^k`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public def twoColorMultiplePartitionCount (ℓ n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n / ℓ + 1),
    Fintype.card (Nat.Partition (n - ℓ * j)) * Fintype.card (Nat.Partition j)

/-- Below `ℓ` the second color is unavailable: `p_{1,ℓ}(n) = p(n)` for `n < ℓ`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public theorem twoColorMultiplePartitionCount_of_lt {ℓ n : ℕ} (h : n < ℓ) :
    twoColorMultiplePartitionCount ℓ n = Fintype.card (Nat.Partition n) := by
  simp [twoColorMultiplePartitionCount, Nat.div_eq_of_lt h]

/-- `p_{1,ℓ}(0) = 1`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public theorem twoColorMultiplePartitionCount_zero (ℓ : ℕ) :
    twoColorMultiplePartitionCount ℓ 0 = 1 := by
  simp [twoColorMultiplePartitionCount]

/-- Congruences for `p_{1,7^k}`: for all `n, β ≥ 0` and `k ≥ 1`,
(6) `p_{1,7^{2k-1}}(7^{2k+β-1} n + (16·7^{2k+β-1} + 7^{2k-1} + 1)/24) ≡ 0 (mod 7^k)`,
(7) `p_{1,7^{2k}}(7^{2k+2β-1} n + (10·7^{2k+2β-1} + 7^{2k} + 1)/24) ≡ 0 (mod 7^{k+β})`,
(8) `p_{1,7^{2k}}(7^{2k+2β} n + (22·7^{2k+2β} + 7^{2k} + 1)/24) ≡ 0 (mod 7^{k+β+1})`,
(9) `p_{1,7^{2k}}(7^{2k+2β+1} n + ((24r + 22)·7^{2k+2β} + 7^{2k} + 1)/24) ≡ 0 (mod 7^{k+β+2})`
for `r ∈ {3, 4, 6}`. Each offset numerator is divisible by `24`, so the natural division is
exact.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 1 (`integers-2026-A94-thm-1`), congruences (6)-(9). -/
public theorem_wanted twoColorMultiplePartitionCount_seven_pow_congr (k β n : ℕ) (hk : 1 ≤ k) :
    7 ^ k ∣ twoColorMultiplePartitionCount (7 ^ (2 * k - 1))
        (7 ^ (2 * k + β - 1) * n + (16 * 7 ^ (2 * k + β - 1) + 7 ^ (2 * k - 1) + 1) / 24) ∧
    7 ^ (k + β) ∣ twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β - 1) * n + (10 * 7 ^ (2 * k + 2 * β - 1) + 7 ^ (2 * k) + 1) / 24) ∧
    7 ^ (k + β + 1) ∣ twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β) * n + (22 * 7 ^ (2 * k + 2 * β) + 7 ^ (2 * k) + 1) / 24) ∧
    ∀ r ∈ ({3, 4, 6} : Finset ℕ), 7 ^ (k + β + 2) ∣ twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β + 1) * n +
          ((24 * r + 22) * 7 ^ (2 * k + 2 * β) + 7 ^ (2 * k) + 1) / 24)


/-- Rows `1`-`7` of Garvan's matrix `M = (m_{i,j})` as printed in Tables 1 and 2 (columns
`1`-`14`); every other entry of these rows is `0`, and the value is `0` for `i = 0` or `j = 0`
or `i > 7`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1, Tables 1 and 2. -/
public def garvanMTable (i j : ℕ) : ℕ :=
  if i = 0 ∨ j = 0 then 0 else
  (([[7, 7 ^ 2],
     [10, 9 * 7 ^ 2, 2 * 7 ^ 4, 7 ^ 5],
     [3, 114 * 7, 85 * 7 ^ 3, 24 * 7 ^ 5, 3 * 7 ^ 7, 7 ^ 8],
     [0, 82 * 7, 176 * 7 ^ 3, 845 * 7 ^ 4, 272 * 7 ^ 6, 46 * 7 ^ 8, 4 * 7 ^ 10, 7 ^ 11],
     [0, 190, 1265 * 7 ^ 2, 1895 * 7 ^ 4, 1233 * 7 ^ 6, 3025 * 7 ^ 7, 620 * 7 ^ 9,
       75 * 7 ^ 11, 5 * 7 ^ 13, 7 ^ 14],
     [0, 27, 736 * 7 ^ 2, 16782 * 7 ^ 3, 20424 * 7 ^ 5, 12825 * 7 ^ 7, 4770 * 7 ^ 9,
       7830 * 7 ^ 10, 1178 * 7 ^ 12, 111 * 7 ^ 14, 6 * 7 ^ 16, 7 ^ 17],
     [0, 1, 253 * 7 ^ 2, 1902 * 7 ^ 4, 4246 * 7 ^ 6, 31540 * 7 ^ 7, 19302 * 7 ^ 9,
       7501 * 7 ^ 11, 1944 * 7 ^ 13, 2397 * 7 ^ 14, 285 * 7 ^ 16, 22 * 7 ^ 18, 7 ^ 20,
       7 ^ 20]] : List (List ℕ)).getD (i - 1) []).getD (j - 1) 0

/-- Garvan's matrix `m_{i,j}` (`i, j ≥ 1`): rows `1`-`7` from Tables 1 and 2
(`garvanMTable`); for `i ≥ 8`, `m_{i,1} = m_{i,2} = 0` and, for `j ≥ 3`,
`m_{i,j} = 7m_{i-3,j-1} + 35m_{i-2,j-1} + 49m_{i-1,j-1} + m_{i-7,j-2} + 7m_{i-6,j-2}
+ 21m_{i-5,j-2} + 49m_{i-4,j-2} + 147m_{i-3,j-2} + 343m_{i-2,j-2} + 343m_{i-1,j-2}`.
Index `0` gives `0`. These are the coefficients of `H(ξ^{-i}) = ∑_j m_{i,j} T^{-j}`
(Lemma 1).

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public def garvanM : ℕ → ℕ → ℕ
  | _ + 8, 0 => 0
  | _ + 8, 1 => 0
  | _ + 8, 2 => 0
  | i + 8, j + 3 =>
      7 * garvanM (i + 5) (j + 2) + 35 * garvanM (i + 6) (j + 2) +
        49 * garvanM (i + 7) (j + 2) + garvanM (i + 1) (j + 1) + 7 * garvanM (i + 2) (j + 1) +
        21 * garvanM (i + 3) (j + 1) + 49 * garvanM (i + 4) (j + 1) +
        147 * garvanM (i + 5) (j + 1) + 343 * garvanM (i + 6) (j + 1) +
        343 * garvanM (i + 7) (j + 1)
  | i, j => garvanMTable i j

/-- `m_{1,1} = 7` and `m_{1,2} = 49` (Table 1).

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1, Table 1. -/
public theorem garvanM_one : garvanM 1 1 = 7 ∧ garvanM 1 2 = 49 := by decide

/-- The first value given by the recurrence: `m_{8,3} = 2464`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public theorem garvanM_eight_three : garvanM 8 3 = 2464 := by decide

/-- The recurrence for `m_{i,j}`, `i ≥ 8`, `j ≥ 3`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public theorem garvanM_rec (i j : ℕ) :
    garvanM (i + 8) (j + 3) =
      7 * garvanM (i + 5) (j + 2) + 35 * garvanM (i + 6) (j + 2) +
        49 * garvanM (i + 7) (j + 2) + garvanM (i + 1) (j + 1) + 7 * garvanM (i + 2) (j + 1) +
        21 * garvanM (i + 3) (j + 1) + 49 * garvanM (i + 4) (j + 1) +
        147 * garvanM (i + 5) (j + 1) + 343 * garvanM (i + 6) (j + 1) +
        343 * garvanM (i + 7) (j + 1) := by
  rw [garvanM]

/-- Garvan's coefficient vectors `x_k = (x_{k,1}, x_{k,2}, …)` (`k ≥ 1`): `x_1 = (7, 7^2, 0, …)`
and `x_{k+1,i} = ∑_{j ≥ 1} x_{k,j} m_{4j,j+i}` for odd `k`, `∑_{j ≥ 1} x_{k,j} m_{4j+1,j+i}`
for even `k`. The sum over `j` is cut at `7^k`: `m_{i,j} = 0` for `j > 2i`, so the support of
`x_{k+1}` is at most `7·(support of x_k) + 2`, below `7^{k+1}`. Index `0` gives `0`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public def garvanX : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, i => if i = 1 then 7 else if i = 2 then 49 else 0
  | k + 2, i => ∑ j ∈ Finset.Icc 1 (7 ^ (k + 1)), garvanX (k + 1) j *
      (if (k + 1) % 2 = 1 then garvanM (4 * j) (j + i) else garvanM (4 * j + 1) (j + i))

/-- `x_1 = (7, 7^2, 0, …)`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Section 1. -/
public theorem garvanX_one : garvanX 1 1 = 7 ∧ garvanX 1 2 = 49 ∧ garvanX 1 3 = 0 := by decide

/-- The coefficient vectors `y^{(2k-1)}_β` of Theorem 2 (`β ≥ 1`): `y^{(2k-1)}_{1,j} = x_{2k-1,j}`
and `y^{(2k-1)}_{β+1,j} = ∑_{i ≥ 1} y^{(2k-1)}_{β,i} m_{4i+1,i+j}`. The sum over `i` is cut at
`7^{2k+β-2}`, above the support of `y^{(2k-1)}_β` (each step maps support `s` into `7s + 2`).
Index `β = 0` gives `0`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 2. -/
public def garvanYOdd (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, j => garvanX (2 * k - 1) j
  | b + 2, j => ∑ i ∈ Finset.Icc 1 (7 ^ (2 * k + b - 1)),
      garvanYOdd k (b + 1) i * garvanM (4 * i + 1) (i + j)

/-- `y^{(2k-1)}_1 = x_{2k-1}`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 2. -/
public theorem garvanYOdd_one (k j : ℕ) : garvanYOdd k 1 j = garvanX (2 * k - 1) j := by
  rw [garvanYOdd]

/-- The coefficient vectors `y^{(2k)}_β` of Theorem 3 (`β ≥ 1`): `y^{(2k)}_{1,j} = x_{2k-1,j}`
and `y^{(2k)}_{β+1,j} = ∑_{i ≥ 1} y^{(2k)}_{β,i} m_{4i,i+j}` for odd `β`,
`∑_{i ≥ 1} y^{(2k)}_{β,i} m_{4i+2,i+j}` for even `β`. The sum over `i` is cut at
`7^{2k+β-2}`, above the support of `y^{(2k)}_β` (each step maps support `s` into `7s + 4`).
Index `β = 0` gives `0`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 3. -/
public def garvanYEven (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, j => garvanX (2 * k - 1) j
  | b + 2, j => ∑ i ∈ Finset.Icc 1 (7 ^ (2 * k + b - 1)), garvanYEven k (b + 1) i *
      (if (b + 1) % 2 = 1 then garvanM (4 * i) (i + j) else garvanM (4 * i + 2) (i + j))

/-- `y^{(2k)}_1 = x_{2k-1}`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 3. -/
public theorem garvanYEven_one (k j : ℕ) : garvanYEven k 1 j = garvanX (2 * k - 1) j := by
  rw [garvanYEven]

/-- **Lemma 1** (Garvan). With `f_k = ∏_{n ≥ 1} (1 - q^{kn})`, `ξ = f_1 / (q^2 f_{49})`,
`T = f_7^4 / (q^7 f_{49}^4)` and `H` the huffing operator `∑ p_n q^n ↦ ∑ p_{7n} q^{7n}`:
`H(ξ^{-i}) = ∑_{j ≥ 1} m_{i,j} T^{-j}` and `H(ξ^{-4i}) = ∑_{j ≥ 1} m_{4i,i+j} T^{-i-j}`, for
`i ≥ 1`. Identity in `ℚ⟦X⟧` (`q = X`, `∏'` in the coefficientwise topology), with
`ξ^{-i} = q^{2i} f_{49}^i / f_1^i` and `T^{-j} = q^{7j} f_{49}^{4j} / f_7^{4j}`; the sums are
cut at `j ≤ 2i`, resp. `j ≤ 7i`, beyond which `m` vanishes.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 1 (`integers-2026-A94-lem-1`). -/
public theorem_wanted huffing_xi_inv_pow_eq_sum_garvanM (i : ℕ) (hi : 1 ≤ i) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    let H : ℚ⟦X⟧ → ℚ⟦X⟧ := fun F => PowerSeries.mk fun n => if 7 ∣ n then coeff n F else 0
    let ξinv : ℕ → ℚ⟦X⟧ := fun a => X ^ (2 * a) * f 49 ^ a * (f 1 ^ a)⁻¹
    let Tinv : ℕ → ℚ⟦X⟧ := fun b => X ^ (7 * b) * f 49 ^ (4 * b) * (f 7 ^ (4 * b))⁻¹
    H (ξinv i) = ∑ j ∈ Finset.Icc 1 (2 * i), (garvanM i j : ℚ⟦X⟧) * Tinv j ∧
      H (ξinv (4 * i)) = ∑ j ∈ Finset.Icc 1 (7 * i), (garvanM (4 * i) (i + j) : ℚ⟦X⟧) * Tinv (i + j)

/-- **Lemma 2.** For `i ≥ 1`, with `f_k`, `H` as in Lemma 1:
`H(q^{i+2} f_7^{4i} / f_1^{4i+1}) = ∑_j m_{4i+1,i+j} q^{7j} f_{49}^{4j-1} / f_7^{4j}`,
`H(q^{i+4} f_7^{4i} / f_1^{4i+2}) = ∑_j m_{4i+2,i+j} q^{7j} f_{49}^{4j-2} / f_7^{4j}` and
`H(q^i f_7^{4i} / f_1^{4i}) = ∑_j m_{4i,i+j} q^{7j} f_{49}^{4j} / f_7^{4j}`. Identities in
`ℚ⟦X⟧`; the sums are cut at `j ≤ 7i + 4`, beyond which `m` vanishes.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 2 (`integers-2026-A94-lem-2`). -/
public theorem_wanted huffing_eta_quotients_eq_sum_garvanM (i : ℕ) (hi : 1 ≤ i) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    let H : ℚ⟦X⟧ → ℚ⟦X⟧ := fun F => PowerSeries.mk fun n => if 7 ∣ n then coeff n F else 0
    H (X ^ (i + 2) * f 7 ^ (4 * i) * (f 1 ^ (4 * i + 1))⁻¹) =
        ∑ j ∈ Finset.Icc 1 (7 * i + 4), (garvanM (4 * i + 1) (i + j) : ℚ⟦X⟧) *
          (X ^ (7 * j) * f 49 ^ (4 * j - 1) * (f 7 ^ (4 * j))⁻¹) ∧
      H (X ^ (i + 4) * f 7 ^ (4 * i) * (f 1 ^ (4 * i + 2))⁻¹) =
        ∑ j ∈ Finset.Icc 1 (7 * i + 4), (garvanM (4 * i + 2) (i + j) : ℚ⟦X⟧) *
          (X ^ (7 * j) * f 49 ^ (4 * j - 2) * (f 7 ^ (4 * j))⁻¹) ∧
      H (X ^ i * f 7 ^ (4 * i) * (f 1 ^ (4 * i))⁻¹) =
        ∑ j ∈ Finset.Icc 1 (7 * i + 4), (garvanM (4 * i) (i + j) : ℚ⟦X⟧) *
          (X ^ (7 * j) * f 49 ^ (4 * j) * (f 7 ^ (4 * j))⁻¹)

/-- **Lemma 3** (Garvan). For `i, j ≥ 1`, `7^{⌊(7j - 2i - 1)/4⌋} ∣ m_{i,j}`, and in particular
`7^{⌊(7j-i-1)/4⌋} ∣ m_{4i,i+j}`, `7^{⌊(7j-i-3)/4⌋} ∣ m_{4i+1,i+j}`,
`7^{⌊(7j-i-5)/4⌋} ∣ m_{4i+2,i+j}`. The paper's `π(n) ≥ e` (`π(0) = ∞`) is stated as
`7^e ∣ n`; `[·]` is read as the floor (the ceiling reading fails: `m_{2,1} = 10` has
`π = 0 < ⌈2/4⌉ = 1`). A negative floor is replaced by
`0` (natural subtraction), which gives the same statement.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 3 (`integers-2026-A94-lem-3`). -/
public theorem_wanted seven_pow_dvd_garvanM (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    7 ^ ((7 * j - 2 * i - 1) / 4) ∣ garvanM i j ∧
      7 ^ ((7 * j - i - 1) / 4) ∣ garvanM (4 * i) (i + j) ∧
      7 ^ ((7 * j - i - 3) / 4) ∣ garvanM (4 * i + 1) (i + j) ∧
      7 ^ ((7 * j - i - 5) / 4) ∣ garvanM (4 * i + 2) (i + j)

/-- **Lemma 4** (Garvan). `π(x_{1,1}) = 1`, `π(x_{1,2}) = 2`, and for `k, j ≥ 1`,
`π(x_{2k+1,j}) ≥ k + 1 + ⌊(7j-4)/4⌋` and `π(x_{2k,j}) ≥ k + 1 + ⌊(7j-6)/4⌋`, with `π` the
`7`-adic valuation (`π(0) = ∞`); the bounds are stated as divisibility.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 4 (`integers-2026-A94-lem-4`). -/
public theorem_wanted seven_pow_dvd_garvanX (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    padicValNat 7 (garvanX 1 1) = 1 ∧ padicValNat 7 (garvanX 1 2) = 2 ∧
      7 ^ (k + 1 + (7 * j - 4) / 4) ∣ garvanX (2 * k + 1) j ∧
      7 ^ (k + 1 + (7 * j - 6) / 4) ∣ garvanX (2 * k) j

/-- **Lemma 5.** For `j, k ≥ 1` and `β ≥ 0`, `π(y^{(2k)}_{2β+1,j}) ≥ k + β + ⌊(7j-7)/4⌋` and
`π(y^{(2k)}_{2β+2,j}) ≥ k + β + 1 + ⌊(7j-7)/4⌋` (`π` the `7`-adic valuation, stated as
divisibility).

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 5 (`integers-2026-A94-lem-5`). -/
public theorem_wanted seven_pow_dvd_garvanYEven (k β j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    7 ^ (k + β + (7 * j - 7) / 4) ∣ garvanYEven k (2 * β + 1) j ∧
      7 ^ (k + β + 1 + (7 * j - 7) / 4) ∣ garvanYEven k (2 * β + 2) j

/-- **Lemma 6.** For `j, k ≥ 1` and `β ≥ 0`, `π(y^{(2k-1)}_{β+1,j}) ≥ k + ⌊(7j-7)/4⌋` (`π` the
`7`-adic valuation, stated as divisibility).

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 6 (`integers-2026-A94-lem-6`). -/
public theorem_wanted seven_pow_dvd_garvanYOdd (k β j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    7 ^ (k + (7 * j - 7) / 4) ∣ garvanYOdd k (β + 1) j

/-- **Theorem 2.** For `β ≥ 0` and `k ≥ 1`,
`∑_n p_{1,7^{2k-1}}(7^{2k+β-1} n + (16·7^{2k+β-1} + 7^{2k-1} + 1)/24) q^n
= ∑_{i ≥ 1} y^{(2k-1)}_{β+1,i} q^{i-1} f_7^{4i-1} / f_1^{4i+1}`, with
`f_k = ∏_{n ≥ 1} (1 - q^{kn})`. Identity in `ℚ⟦X⟧` (`q = X`, `∏'` in the coefficientwise
topology); the sum over `i` is cut at `7^{2k+β-1}`, above the support of `y^{(2k-1)}_{β+1}`.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 2 (`integers-2026-A94-thm-2`). -/
public theorem_wanted twoColorMultiplePartitionCount_seven_pow_odd_generatingFunction
    (k β : ℕ) (hk : 1 ≤ k) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    PowerSeries.mk (fun n => (twoColorMultiplePartitionCount (7 ^ (2 * k - 1))
        (7 ^ (2 * k + β - 1) * n + (16 * 7 ^ (2 * k + β - 1) + 7 ^ (2 * k - 1) + 1) / 24) : ℚ)) =
      ∑ i ∈ Finset.Icc 1 (7 ^ (2 * k + β - 1)), (garvanYOdd k (β + 1) i : ℚ⟦X⟧) *
        (X ^ (i - 1) * f 7 ^ (4 * i - 1) * (f 1 ^ (4 * i + 1))⁻¹)

/-- **Theorem 3.** For `β ≥ 0` and `k ≥ 1`, with `f_k` as in Theorem 2,
`∑_n p_{1,7^{2k}}(7^{2k+2β-1} n + (10·7^{2k+2β-1} + 7^{2k} + 1)/24) q^n
= ∑_{i ≥ 1} y^{(2k)}_{2β+1,i} q^{i-1} f_7^{4i-2} / f_1^{4i}` and
`∑_n p_{1,7^{2k}}(7^{2k+2β} n + (22·7^{2k+2β} + 7^{2k} + 1)/24) q^n
= ∑_{j ≥ 1} y^{(2k)}_{2β+2,j} q^{j-1} f_7^{4j} / f_1^{4j+2}`. Identities in `ℚ⟦X⟧`; the sums
are cut at `7^{2k+2β}`, resp. `7^{2k+2β+1}`, above the supports of the vectors.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 3 (`integers-2026-A94-thm-3`). -/
public theorem_wanted twoColorMultiplePartitionCount_seven_pow_even_generatingFunction
    (k β : ℕ) (hk : 1 ≤ k) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    PowerSeries.mk (fun n => (twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β - 1) * n + (10 * 7 ^ (2 * k + 2 * β - 1) + 7 ^ (2 * k) + 1) / 24) :
          ℚ)) =
        ∑ i ∈ Finset.Icc 1 (7 ^ (2 * k + 2 * β)), (garvanYEven k (2 * β + 1) i : ℚ⟦X⟧) *
          (X ^ (i - 1) * f 7 ^ (4 * i - 2) * (f 1 ^ (4 * i))⁻¹) ∧
      PowerSeries.mk (fun n => (twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β) * n + (22 * 7 ^ (2 * k + 2 * β) + 7 ^ (2 * k) + 1) / 24) : ℚ)) =
        ∑ j ∈ Finset.Icc 1 (7 ^ (2 * k + 2 * β + 1)), (garvanYEven k (2 * β + 2) j : ℚ⟦X⟧) *
          (X ^ (j - 1) * f 7 ^ (4 * j) * (f 1 ^ (4 * j + 2))⁻¹)

end

end MetaMathlibExt
