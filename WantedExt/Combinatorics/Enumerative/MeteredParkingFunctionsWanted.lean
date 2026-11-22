/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

namespace MetaMathlibExt

@[expose] public section

/-!
Conventions for the statements below. Spots and preferences are zero-based: preference
`f i : Fin n` and spot `s` are the source's `f i + 1` and `s + 1`, and car `i : Fin m` is the
source's car `i + 1`. Classical `(m, n)`-parking functions are MathlibExt's
`IsPartialParkingFunction m n` (and `IsParkingFunction n` for `m = n`).
-/

/-- The outcome of the `t`-metered parking scheme on `n` spots (zero-based) for the preference
list `prefs`: cars arrive in order; car `i` takes the least spot `s` with `prefs[i] ≤ s < n` not
occupied by one of the previous `t` cars (cars `i - t, …, i - 1` that parked), giving `some s`, or
fails, giving `none`. After car `j` parks, car `j - t` leaves, so only the last `t` entries of the
outcome so far are occupied.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of the `t`-metered scheme) and
Section 2
(definition of the outcome). -/
public def meteredOutcome (t n : ℕ) (prefs : List ℕ) : List (Option ℕ) :=
  prefs.foldl
    (fun out a => out ++ [(List.range' a (n - a)).find?
      (fun s => decide (s ∉ (out.drop (out.length - t)).filterMap id))])
    []

/-- The source's example with `t = 1`, `n = 2` and preferences `(1,1,1)`: cars park in spots
`1, 2, 1`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of `t`-metered parking
functions (Section 1). -/
public theorem meteredOutcome_one_two_ones :
    meteredOutcome 1 2 [0, 0, 0] = [some 0, some 1, some 0] := by decide

/-- The source's example with `t = 1`, `n = 2` and preferences `(1,1,2)`: car `3` fails.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of `t`-metered parking
functions (Section 1). -/
public theorem meteredOutcome_one_two_fail :
    meteredOutcome 1 2 [0, 0, 1] = [some 0, some 1, none] := by decide

/-- The source's example `O^2_6(3,3,3,3,4,5,6) = (3,4,5,3,4,5,6)` and
`O^1_6(3,3,3,3,4,5,6) = (3,4,3,4,5,6,X)`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of the outcome
(Section 2). -/
public theorem meteredOutcome_example_six :
    meteredOutcome 2 6 [2, 2, 2, 2, 3, 4, 5] =
        [some 2, some 3, some 4, some 2, some 3, some 4, some 5] ∧
      meteredOutcome 1 6 [2, 2, 2, 2, 3, 4, 5] =
        [some 2, some 3, some 2, some 3, some 4, some 5, none] := by decide

/-- A `t`-metered `(m, n)`-parking function: every car parks under the `t`-metered scheme.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of `t`-metered parking
functions). -/
public def IsMeteredParkingFunction {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) : Prop :=
  ∀ o ∈ meteredOutcome t n (List.ofFn fun i => (f i : ℕ)), o ≠ none

/-- Decidability of `IsMeteredParkingFunction` (a finite check of the outcome list).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of `t`-metered parking
functions). -/
public instance {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) :
    Decidable (IsMeteredParkingFunction t f) := by
  unfold IsMeteredParkingFunction
  infer_instance

/-- The source's `mpf_{m,n}(t)`: the number of `t`-metered `(m, n)`-parking functions.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition and the notation
`mpf_{m,n}(t)`). -/
public def meteredParkingCount (t m n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction t f).card

/-- `mpf_{2,2}(1) = 3`, an entry of the source's Table 1.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Table 1. -/
public theorem meteredParkingCount_one_two_two : meteredParkingCount 1 2 2 = 3 := by decide

/-- The number of lucky cars (cars parking in their preferred spot) of `f` under the `t`-metered
scheme.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 2 (`lucky(α)`). -/
public def meteredLuckyCount {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) : ℕ :=
  ((List.ofFn fun i => (f i : ℕ)).zip (meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))).countP
    fun p => decide (p.2 = some p.1)

/-- One step of the lace decomposition: append `a` to the last lace if that keeps it a lace
(`(p)` extends by `p`, `(p, p, p+1, …, e)` extends by `e + 1`), otherwise start a new lace `(a)`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace
decomposition). -/
public def laceStep (acc : List (List ℕ)) (a : ℕ) : List (List ℕ) :=
  match acc.getLast? with
  | some [p] => if a = p then acc.dropLast ++ [[p, a]] else acc ++ [[a]]
  | some l@(_ :: _ :: _) =>
      if a = l.getLastD 0 + 1 then acc.dropLast ++ [l ++ [a]] else acc ++ [[a]]
  | _ => acc ++ [[a]]

/-- The lace decomposition of a sequence: its partition, from left to right, into maximally long
laces of consecutive entries, where a lace is `(p)` or `(p, p, p+1, …, p+ℓ-2)`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace
decomposition). -/
public def laceDecomposition (l : List ℕ) : List (List ℕ) :=
  l.foldl laceStep []

/-- The source's examples `lace(3,3,3,3,4,6) = ((3,3),(3,3,4),(6))` and
`lace(4,1,2,2,3,4,5,5,1,2) = ((4),(1),(2,2,3,4,5),(5),(1),(2))`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3, example after the definition of the lace
decomposition. -/
public theorem laceDecomposition_examples :
    laceDecomposition [3, 3, 3, 3, 4, 6] = [[3, 3], [3, 3, 4], [6]] ∧
      laceDecomposition [4, 1, 2, 2, 3, 4, 5, 5, 1, 2] =
        [[4], [1], [2, 2, 3, 4, 5], [5], [1], [2]] := by decide

/-- A necessary condition: if `f` is a `t`-metered `(m, n)`-parking function then for every spot
`i ∈ [n]` and every `j ∈ [m - t]`, `|{j ≤ k ≤ j + t : a_k ≤ i}| ≥ t + 1 - n + i`, stated with
`n` moved to the left (`t + 1 + i ≤ |…| + n`) and one-based `i`, `j`, `k`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 1 (`integers-2025-A73-prop-1`). -/
public theorem_wanted metered_window_count_ge {m n t : ℕ} {f : Fin m → Fin n}
    (hf : IsMeteredParkingFunction t f) (i j : ℕ) (hi : i ∈ Finset.Icc 1 n)
    (hj : j ∈ Finset.Icc 1 (m - t)) :
    t + 1 + i ≤
      (Finset.univ.filter fun k : Fin m =>
          j ≤ (k : ℕ) + 1 ∧ (k : ℕ) + 1 ≤ j + t ∧ (f k : ℕ) + 1 ≤ i).card + n

/-- If `m > n` and `t ≥ n`, there are no `t`-metered `(m, n)`-parking functions.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 2 (`integers-2025-A73-prop-2`). -/
public theorem_wanted meteredParkingCount_eq_zero {m n t : ℕ} (hmn : n < m) (htn : n ≤ t) :
    meteredParkingCount t m n = 0

/-- If `t ≥ m - 1` and `n ≥ m`, the `t`-metered `(m, n)`-parking functions are exactly the
classical `(m, n)`-parking functions.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 3 (`integers-2025-A73-prop-3`). -/
public theorem_wanted isMeteredParkingFunction_iff_of_le {m n t : ℕ} (ht : m - 1 ≤ t)
    (hmn : m ≤ n) (f : Fin m → Fin n) :
    IsMeteredParkingFunction t f ↔ IsPartialParkingFunction m n f

/-- For `m ≤ n`, every classical `(m, n)`-parking function is a `t`-metered parking function for
every `t ≥ 0`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 4 (`integers-2025-A73-prop-4`). -/
public theorem_wanted IsPartialParkingFunction.isMeteredParkingFunction {m n : ℕ} (hmn : m ≤ n)
    {f : Fin m → Fin n} (hf : IsPartialParkingFunction m n f) (t : ℕ) :
    IsMeteredParkingFunction t f

/-- Under the `t`-metered scheme, a car that parks has displacement at most `t`, and a car that
fails to park has preference `a_i ≥ n - t + 1` (zero-based: `n ≤ f i + t`).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 5 (`integers-2025-A73-prop-5`). -/
public theorem_wanted meteredOutcome_displacement_le {m n t : ℕ} (f : Fin m → Fin n) (i : Fin m) :
    (∀ s, (meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))[(i : ℕ)]? = some (some s) →
        s ≤ (f i : ℕ) + t) ∧
      ((meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))[(i : ℕ)]? = some none →
        n ≤ (f i : ℕ) + t)

/-- `mpf_{m,n}(t) ≥ (n - t)^m` for all `m, n, t`, with truncated subtraction `n - t` in `ℕ`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 1 (`integers-2025-A73-cor-1`). -/
public theorem_wanted pow_sub_le_meteredParkingCount (t m n : ℕ) :
    (n - t) ^ m ≤ meteredParkingCount t m n

/-- For every `t ≥ 1`, `mpf_{2,n}(t) = n^2 - 1`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 2 (`integers-2025-A73-cor-2`). -/
public theorem_wanted meteredParkingCount_two {t : ℕ} (ht : 1 ≤ t) (n : ℕ) :
    meteredParkingCount t 2 n = n ^ 2 - 1

/-- For `0 < m ≤ n` and `t = 1`, car `i` is lucky (parks in its preference) if and only if `a_i`
is the first entry of a lace of `lace(α)`; equivalently car `i` is displaced (by one, or fails at
spot `n`) exactly when `a_i` is not the first entry of its lace. Stated as equality of the
lucky-indicator list with the lace-start pattern.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 1 (`integers-2025-A73-lem-1`). -/
public theorem_wanted one_metered_lucky_iff_lace_start {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (f : Fin m → Fin n) :
    ((List.ofFn fun i => (f i : ℕ)).zip (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ)))).map
        (fun p => decide (p.2 = some p.1)) =
      (laceDecomposition (List.ofFn fun i => (f i : ℕ))).flatMap
        fun c => true :: List.replicate (c.length - 1) false

/-- For `0 < m ≤ n`, `f` is a `1`-metered `(m, n)`-parking function if and only if every instance
of `n` (zero-based `n - 1`) in `f` is the first entry of a lace of `lace(f)`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 1 (`integers-2025-A73-thm-1`). -/
public theorem_wanted isMeteredParkingFunction_one_iff_lace {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (f : Fin m → Fin n) :
    IsMeteredParkingFunction 1 f ↔
      ∀ c ∈ laceDecomposition (List.ofFn fun i => (f i : ℕ)), n - 1 ∉ c.tail

/-- For `m ≥ 1`, `f : [m] → [2]` is a `1`-metered `(m, 2)`-parking function if and only if every
lace of `lace(f)` containing a `2` (zero-based `1`) is a singleton.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 3 (`integers-2025-A73-cor-3`). -/
public theorem_wanted isMeteredParkingFunction_one_two_iff_lace {m : ℕ} (hm : 1 ≤ m)
    (f : Fin m → Fin 2) :
    IsMeteredParkingFunction 1 f ↔
      ∀ c ∈ laceDecomposition (List.ofFn fun i => (f i : ℕ)), 1 ∈ c → c.length = 1

/-- If `1 ≤ m ≤ j < k ≤ n`, the `1`-metered `(m, n)`-parking functions whose last car parks in
spot `j` are as many as those whose last car parks in spot `k` (one-based `j`, `k`).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 2 (`integers-2025-A73-lem-2`). -/
public theorem_wanted one_metered_last_spot_card_eq {m n j k : ℕ} (hm : 1 ≤ m) (hmj : m ≤ j)
    (hjk : j < k) (hkn : k ≤ n) :
    (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction 1 f ∧
        (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ))).getLast? = some (some (j - 1))).card =
      (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction 1 f ∧
        (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ))).getLast? = some (some (k - 1))).card

/-- For `1 ≤ m ≤ n`, `mpf_{m-1,n}(1)` counts the `1`-metered `(m, n)`-parking functions whose last
car parks in spot `n` (zero-based `n - 1`). The source leaves `1 ≤ m` implicit (a last car).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 3 (`integers-2025-A73-lem-3`). -/
public theorem_wanted one_metered_last_spot_n_card {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction 1 f ∧
        (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ))).getLast? = some (some (n - 1))).card =
      meteredParkingCount 1 (m - 1) n

/-- The Lucas-type recursion for `1`-metered parking functions: `mpf_{1,n}(1) = n`,
`mpf_{0,n}(1) = 1`, and `mpf_{m+1,n}(1) = n · mpf_{m,n}(1) - mpf_{m-1,n}(1)` for `1 ≤ m ≤ n`
(stated in `ℤ`).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 2 (`integers-2025-A73-thm-2`). -/
public theorem_wanted meteredParkingCount_one_recursion (n : ℕ) :
    meteredParkingCount 1 1 n = n ∧ meteredParkingCount 1 0 n = 1 ∧
      ∀ m, 1 ≤ m → m ≤ n →
        (meteredParkingCount 1 (m + 1) n : ℤ) =
          n * meteredParkingCount 1 m n - meteredParkingCount 1 (m - 1) n

/-- For `n > 2`, `mpf_{n,n}(1) = ∑_{k=0}^{n} (n-2)^{n-k} binom(2n+1-k, k)`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 4 (`integers-2025-A73-cor-4`). -/
public theorem_wanted meteredParkingCount_one_diag {n : ℕ} (hn : 2 < n) :
    meteredParkingCount 1 n n =
      ∑ k ∈ Finset.range (n + 1), (n - 2) ^ (n - k) * (2 * n + 1 - k).choose k

/-- For `m ≤ n + 1` and `n > 2`, the Binet form
`mpf_{m,n}(1) = (n(n+√(n²-4)) - 2)/(n(n+√(n²-4)) - 4) · ((n+√(n²-4))/2)^m
  + (n(n-√(n²-4)) - 2)/(n(n-√(n²-4)) - 4) · ((n-√(n²-4))/2)^m`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 5 (`integers-2025-A73-cor-5`). -/
public theorem_wanted meteredParkingCount_one_binet {m n : ℕ} (hm : m ≤ n + 1) (hn : 2 < n) :
    (meteredParkingCount 1 m n : ℝ) =
      (n * (n + Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n + Real.sqrt (n ^ 2 - 4)) - 4) *
          ((n + Real.sqrt (n ^ 2 - 4)) / 2) ^ m +
        (n * (n - Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n - Real.sqrt (n ^ 2 - 4)) - 4) *
          ((n - Real.sqrt (n ^ 2 - 4)) / 2) ^ m

/-- For `n ≥ 2`, `mpf_{3,n}(1) = n^3 - 2n`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 7 (`integers-2025-A73-prop-7`). -/
public theorem_wanted meteredParkingCount_one_three {n : ℕ} (hn : 2 ≤ n) :
    meteredParkingCount 1 3 n = n ^ 3 - 2 * n

/-- For `m, n ≥ 2` and `t ≤ m - 1`, the number of `t`-metered `(m, n)`-parking functions in which
every car is lucky is `n!/(n-t)! · (n-t)^{m-t}`, written `n.descFactorial t * (n - t)^(m - t)`
(equal to `n!/(n-t)!` for `t ≤ n`, and `0` for `t > n`, where the count is also `0`). The source's
companion formula (12) for exactly one lucky car is not stated: it is false as printed when
`m > n + 1` (`n = 2`, `m = 4`, `t = 1`: count `0`, formula `(t-1)!(n-m+1)t^{m-t} = -1`).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 8, Equation (13)
(`integers-2025-A73-prop-8`). -/
public theorem_wanted metered_all_lucky_card {m n t : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (ht : t ≤ m - 1) :
    (Finset.univ.filter fun f : Fin m → Fin n =>
        IsMeteredParkingFunction t f ∧ meteredLuckyCount t f = m).card =
      n.descFactorial t * (n - t) ^ (m - t)

/-- For `2 < m ≤ n + 1`, the closed form of `mpf_{m,n}(m-2)`:
`(n-m+2)^2 (m-1)^{m-3} + ∑_{k=n-m+3}^{n} binom(m-2, n-k) (n-k+1)^{n-k-1} [binom(k+1, 2)(n-m+2)
k^{m-n+k-3} + (k(n-m+1) - binom(n-m+2, 2))(k-n+m-1)^{k-n+m-3} + ∑_{j=n-m+2}^{k-1}
(jk - binom(j+1, 2)) binom(m-2-n+k, k-1-j)(n-m+1) j^{j+m-2-n} (k-j)^{k-j-2}]`. Stated in `ℕ`:
every subtraction is nonnegative on the summation ranges except the exponents of the bases
`n - k + 1 = 1` (at `k = n`) and `k - j = 1` (at `j = k - 1`), where the source's `1^{-1}` and
the truncated `1^0` agree. Formula taken from the arXiv source (the text layer is garbled).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 5 (`integers-2025-A73-thm-5`). -/
public theorem_wanted meteredParkingCount_sub_two {m n : ℕ} (hm : 2 < m) (hmn : m ≤ n + 1) :
    meteredParkingCount (m - 2) m n =
      (n + 2 - m) ^ 2 * (m - 1) ^ (m - 3) +
        ∑ k ∈ Finset.Icc (n + 3 - m) n,
          (m - 2).choose (n - k) * (n - k + 1) ^ (n - k - 1) *
            ((k + 1).choose 2 * (n + 2 - m) * k ^ (m + k - n - 3) +
              (k * (n + 1 - m) - (n + 2 - m).choose 2) * (k + m - n - 1) ^ (k + m - n - 3) +
              ∑ j ∈ Finset.Ico (n + 2 - m) k,
                (j * k - (j + 1).choose 2) * (m + k - 2 - n).choose (k - 1 - j) * (n + 1 - m) *
                  j ^ (j + m - 2 - n) * (k - j) ^ (k - j - 2))

/-- For `1 ≤ m ≤ n`, the number of classical `(m, n)`-parking functions with first entry
`a_1 = j > n - m + 1` is `∑_{i=j}^{n} binom(m-1, n-i)(n-m+1) i^{i+m-n-2} (n-i+1)^{n-i-1}`, and
with `a_1 = j ≤ n - m + 1` it is `m^{m-2} + ∑_{i=n-m+2}^{n}` of the same summand. The text prints
the factor as `(n - m - 1)`, which is false (`m = n = 2`, `j = 1`: two parking functions, formula
`0`); the factor `n - m + 1` is the one in the source's Lemma 4 (`|Sh_m(k-1, n-k)|`), from which
the source derives this corollary, and it matches exact counts. Stated in `ℕ` (the only negative
exponents are `1^{-1}` at `i = n` and `m = 1`, equal to the truncated `1^0`).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 6 (`integers-2025-A73-cor-6`). -/
public theorem_wanted parkingFunction_first_entry_card {m n j : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hj : j ∈ Finset.Icc 1 n) :
    (Finset.univ.filter fun f : Fin m → Fin n =>
        IsPartialParkingFunction m n f ∧ (f ⟨0, hm⟩ : ℕ) + 1 = j).card =
      if n - m + 1 < j then
        ∑ i ∈ Finset.Icc j n, (m - 1).choose (n - i) * (n - m + 1) * i ^ (i + m - n - 2) *
          (n - i + 1) ^ (n - i - 1)
      else
        m ^ (m - 2) + ∑ i ∈ Finset.Icc (n - m + 2) n, (m - 1).choose (n - i) * (n - m + 1) *
          i ^ (i + m - n - 2) * (n - i + 1) ^ (n - i - 1)

/-- For `m ≥ 2` (written `m = k + 2`), `mpf_{m,m-1}(m-2)` equals the sum of the first entries of
all classical parking functions of length `m - 1`, and equals
`∑_{i=1}^{m-1} ∑_{s=0}^{m-1-i} binom(m-2, s) i (s+1)^{s-1} (m-s-1)^{m-s-3}`. Stated in `ℕ` (the
only negative exponents are `1^{-1}` at `s = 0` and `s = m - 2`, equal to the truncated `1^0`).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 7 (`integers-2025-A73-cor-7`). -/
public theorem_wanted meteredParkingCount_sub_two_pred (k : ℕ) :
    meteredParkingCount k (k + 2) (k + 1) =
        ∑ f ∈ Finset.univ.filter (fun f : Fin (k + 1) → Fin (k + 1) => IsParkingFunction (k + 1) f),
          ((f 0 : ℕ) + 1) ∧
      meteredParkingCount k (k + 2) (k + 1) =
        ∑ i ∈ Finset.Icc 1 (k + 1), ∑ s ∈ Finset.range (k + 2 - i),
          k.choose s * i * (s + 1) ^ (s - 1) * (k + 1 - s) ^ (k - 1 - s)

/-- `(π_2, …, π_m)` (zero-based values `π i`, length `m - 1` written `m'`, so `m = m' + 1`) lies in
the parking-function shuffle set `Sh_m(k - 1, n - k)`: it is a shuffle of a word
`α ∈ PF_{m-n+k-1, k-1}` and `β + (k)^{n-k}` with `β ∈ PF_{n-k, n-k}`. Since the entries of `α`
are `≤ k - 1` and those of `β + (k)^{n-k}` are `≥ k + 1` (one-based), such a shuffle is split by
value and parking-function membership does not depend on the order of the entries, so this is
stated as: no entry equals `k`; exactly `m - n + k - 1` entries are `< k` and they form a
parking function on the spots `1, …, k - 1` (at most `k - 1 - j` of them prefer zero-based spot
`j` or later); exactly `n - k` entries are `> k` and, shifted down by `k`, they form a classical
parking function on `n - k` spots (at most `n - j` of them prefer zero-based spot `j`, `k ≤ j < n`,
or later).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4, Definition of `(m, n)`-parking function
shuffles (`Sh_m(k - 1, n - k)`). -/
public def IsParkingShuffle (m' n k : ℕ) (π : Fin m' → Fin n) : Prop :=
  (∀ i, (π i : ℕ) + 1 ≠ k) ∧
    (Finset.univ.filter fun i => (π i : ℕ) + 1 < k).card = m' + 1 + k - n - 1 ∧
    (Finset.univ.filter fun i => k < (π i : ℕ) + 1).card = n - k ∧
    (∀ j < k - 1, (Finset.univ.filter fun i => j ≤ (π i : ℕ) ∧ (π i : ℕ) < k - 1).card ≤
      k - 1 - j) ∧
    ∀ j ∈ Finset.Ico k n, (Finset.univ.filter fun i => j ≤ (π i : ℕ)).card ≤ n - j

/-- Membership in the parking-function shuffle set is decidable.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4 (`Sh_m(k - 1, n - k)`). -/
public instance (m' n k : ℕ) (π : Fin m' → Fin n) : Decidable (IsParkingShuffle m' n k π) := by
  unfold IsParkingShuffle
  infer_instance

/-- Characteristic example: `(3, 7, 2, 1, 7, 2)` (one-based) is a `(7, 8)`-parking function shuffle
with `k = 6`, a shuffle of `(3, 2, 1, 2) ∈ PF_{4,5}` and `(7, 7) = (1, 1) + (6, 6)`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4, Example 5. -/
public theorem isParkingShuffle_example :
    IsParkingShuffle 6 8 6 ![2, 6, 1, 0, 6, 1] := by
  unfold IsParkingShuffle
  decide

/-- Parking-function shuffles and the first entry: for `m ≤ n` and `1 ≤ k ≤ n`, the set
`A^n_{(π_2, …, π_m)} = {j : (j, π_2, …, π_m) ∈ PF_{m,n}}` equals `[k]` if and only if
`(π_2, …, π_m) ∈ Sh_m(k - 1, n - k)`. Zero-based: `A = {j : j < k}`; `m = m' + 1`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 3 (`integers-2025-A73-thm-3`), with
Definition 6 (the sets `A^n`). -/
public theorem_wanted firstEntrySet_eq_iff_isParkingShuffle {m' n k : ℕ} (hmn : m' + 1 ≤ n)
    (hk : k ∈ Finset.Icc 1 n) (π : Fin m' → Fin n) :
    (Finset.univ.filter fun j : Fin n => IsPartialParkingFunction (m' + 1) n (Fin.cons j π)) =
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < k) ↔
      IsParkingShuffle m' n k π

/-- The number of parking-function shuffles: for `m ≤ n` and `1 ≤ k ≤ n`,
`|Sh_m(k - 1, n - k)|` is `binom(m-1, n-k) (n-m+1) k^{m-n+k-2} (n-k+1)^{n-k-1}` if
`k > n - m + 1`, `m^{m-2}` if `k = n - m + 1`, and `0` if `k < n - m + 1`. Stated in `ℕ` with
`m = m' + 1`; the only negative exponents are `1^{-1}` (at `k = n`, and `m = 1`), equal to the
truncated `1^0`.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 4 (`integers-2025-A73-lem-4`). -/
public theorem_wanted isParkingShuffle_card {m' n k : ℕ} (hmn : m' + 1 ≤ n)
    (hk : k ∈ Finset.Icc 1 n) :
    (Finset.univ.filter fun π : Fin m' → Fin n => IsParkingShuffle m' n k π).card =
      if n - (m' + 1) + 1 < k then
        m'.choose (n - k) * (n - (m' + 1) + 1) * k ^ (m' + 1 + k - n - 2) *
          (n - k + 1) ^ (n - k - 1)
      else if k = n - (m' + 1) + 1 then (m' + 1) ^ (m' + 1 - 2)
      else 0

/-- Characterization of `(m - 2)`-metered `(m, n)`-parking functions for `2 < m ≤ n + 1`: let
`(a_2, …, a_{m-1}) ∈ Sh_{m-1}(k - 1, n - k)` for some `k ∈ [n]`; when `m ≤ n` let `j ∈ [k - 1]`
be such that the subsequence `σ` of the entries of `(a_2, …, a_{m-1})` that are less than `k`
lies in `Sh_{m-n+k-1}(j - 1, k - j - 1)`, and when `m = n + 1` let `j = 0`. Then `α` is an
`(m - 2)`-metered parking function iff `a_1 ≤ j` and `a_m ≤ k`, or `j < a_1 ≤ k` and
`a_m ≤ a_1` (one-based `a_i = f i + 1`). The shuffle sets are `IsParkingShuffle` (`m = m' + 1`);
the subsequence `σ`, of length `m - n + k - 2` (the source's first subscript `m - n + k - 1` is
a misprint for this length), is given as a function whose values list equals the filtered list.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 4 (`integers-2025-A73-thm-4`). -/
public theorem_wanted isMeteredParkingFunction_sub_two_iff {m n k j : ℕ} (hm : 2 < m)
    (hmn : m ≤ n + 1) (f : Fin m → Fin n) (hk : k ∈ Finset.Icc 1 n)
    (hsh : IsParkingShuffle (m - 2) n k fun i => f ⟨(i : ℕ) + 1, by have := i.2; omega⟩)
    (hj : (m = n + 1 ∧ j = 0) ∨
      (m ≤ n ∧ j ∈ Finset.Icc 1 (k - 1) ∧
        ∃ σ : Fin (m + k - n - 2) → Fin (k - 1),
          List.ofFn (fun i => (σ i : ℕ)) =
              (List.ofFn fun i : Fin (m - 2) =>
                (f ⟨(i : ℕ) + 1, by have := i.2; omega⟩ : ℕ)).filter (fun x => x + 1 < k) ∧
            IsParkingShuffle (m + k - n - 2) (k - 1) j σ)) :
    IsMeteredParkingFunction (m - 2) f ↔
      ((f ⟨0, by omega⟩ : ℕ) + 1 ≤ j ∧ (f ⟨m - 1, by omega⟩ : ℕ) + 1 ≤ k) ∨
        (j < (f ⟨0, by omega⟩ : ℕ) + 1 ∧ (f ⟨0, by omega⟩ : ℕ) + 1 ≤ k ∧
          (f ⟨m - 1, by omega⟩ : ℕ) ≤ f ⟨0, by omega⟩)

/-- Characterization of `(n - 1)`-metered `(n + k, n)`-parking functions for `k > 0`: `α` is one
iff its first `n` entries form a classical parking function (MathlibExt's threshold form of
`a'_i ≤ i` for the non-decreasing rearrangement) and, with `(π_1, …, π_n)` the
`(n - 1)`-metered outcome of `(a_1, …, a_n)`, `a_{n+i} ≤ π_{i mod n}` for all `i ∈ [k]`. The index
`i mod n` is read with representatives `1, …, n` (zero-based `i % n`), as the proof describes the
periodic outcome `(π_1, …, π_n, π_1, …)`; the printed `π_{n mod n} = π_0` is undefined.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 6 (`integers-2025-A73-thm-6`). -/
public theorem_wanted isMeteredParkingFunction_pred_iff {n k : ℕ} (hk : 0 < k)
    (f : Fin (n + k) → Fin n) :
    IsMeteredParkingFunction (n - 1) f ↔
      IsParkingFunction n (fun i => f (Fin.castAdd k i)) ∧
        ∀ i : Fin k, ∃ s, (meteredOutcome (n - 1) n
            (List.ofFn fun i : Fin n => (f (Fin.castAdd k i) : ℕ)))[(i : ℕ) % n]? = some (some s) ∧
          (f (Fin.natAdd n i) : ℕ) ≤ s

end

end MetaMathlibExt
