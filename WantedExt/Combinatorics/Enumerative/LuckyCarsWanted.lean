/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lucky cars and lucky spots in parking functions

Statements from Steve Butler, Kimberly Hadaway, Victoria
Lenius, Preston Martens, and Marshall Moats, "Lucky Cars and
Lucky Spots in Parking Functions", *Journal of Integer
Sequences* 29 (2026), Article 26.1.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex>).

Parking functions are MathlibExt's
`MetaMathlibExt.IsParkingFunction n f` for
`f : Fin n → Fin n` (zero-based: car `i` and spot `j` below
are the paper's `(i+1)`-st car and `(j+1)`-st spot). The
greedy parking outcome is `parkSpots`: cars arrive in order
and each takes the least free spot at or after its preference
(`nextFreeSpot`, defaulting to the preference itself when no
spot is free, which does not occur for parking functions). Car
`i` is *lucky* when it parks in its preferred spot
(`IsLuckyCar`), spot `j` is lucky when some car preferring it
parks there, and `q n i j`, `qInc n i j`, `qDec n i j` are the
paper's `q_n(i+1, j+1)`, `q_n^i(i+1, j+1)`, `q_n^d(i+1, j+1)`:
the numbers of (all, weakly increasing, weakly decreasing)
parking functions in which car `i` prefers spot `j` and is
lucky. Counts with possibly negative exponents are stated in
`ℚ` with `zpow`.

Two records are already proved in MathlibExt and are not
restated: Proposition 8 (Pollak's partial count) is
`MetaMathlibExt.pollak_partial_parking_functions_card`, and
Corollary 19 (expected lucky spots, weakly increasing case)
is
`MetaMathlibExt.expected_lucky_spots_weakly_increasing_parking_functions`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt Polynomial

/-- The least spot at or after `a` not in `occ`, defaulting to
`a` when there is none. -/
def nextFreeSpot {n : ℕ} (occ : Finset (Fin n)) (a : Fin n) : Fin n :=
  if h : (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).Nonempty then
    (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).min' h
  else a

/-- The spots taken by greedily parking the preference list
`(List.ofFn f)`, in arrival order. -/
def parkSpotsFrom {n : ℕ} : List (Fin n) → Finset (Fin n) → List (Fin n)
  | [], _ => []
  | a :: rest, occ =>
      nextFreeSpot occ a ::
        parkSpotsFrom rest (insert (nextFreeSpot occ a) occ)

/-- The greedy parking outcome of `f`: the spot each car
ends in. -/
def parkSpots {n : ℕ} (f : Fin n → Fin n) : Fin n → Fin n :=
  fun i => (parkSpotsFrom (List.ofFn f) ∅).getD i.val i

/-- Car `i` is lucky: it parks in its preferred spot. -/
def IsLuckyCar {n : ℕ} (f : Fin n → Fin n) (i : Fin n) : Prop :=
  parkSpots f i = f i

/-- The number of lucky cars of `f`. -/
def luckyCount {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  (Finset.univ.filter (fun i => decide (parkSpots f i = f i))).card

/-- The paper's `q_n(i+1, j+1)`: parking functions of length
`n` in which car `i` prefers spot `j` and is lucky. -/
noncomputable def q (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ f i = j ∧ IsLuckyCar f i }

/-- The paper's `q_n^i(i+1, j+1)`: weakly increasing parking
functions in which car `i` prefers spot `j` and is lucky. -/
noncomputable def qInc (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Monotone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- The paper's `q_n^d(i+1, j+1)`: weakly decreasing parking
functions in which car `i` prefers spot `j` and is lucky. -/
noncomputable def qDec (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- The paper's polynomial
`f(x) = (1/(n+1)) ∏_{i=1}^n ((n+2-i)x + (i-1))` in `ℚ[x]`
(zero-based product: `(n+1-i)x + i` for `i : Fin n`). -/
noncomputable def luckyGenPoly (n : ℕ) : Polynomial ℚ :=
  C (1 / (n + 1 : ℚ)) *
    ∏ i : Fin n, (C ((n + 1 - i.val : ℕ) : ℚ) * X + C (i.val : ℚ))

/-- **Theorem 4**: for disjoint `L, U ⊆ [n]`, the number of
parking functions in which the cars in `L` are lucky and the
cars in `U` are not is
`(∏_{i ∈ L} (n+2-i)) (∏_{i ∈ U} (i-1)) (n+1)^{n-|L|-|U|-1}`
(paper's one-based indices; here `i.val` is one less).

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 4. -/
theorem_wanted card_parking_lucky_on (n : ℕ) (L U : Finset (Fin n))
    (hLU : Disjoint L U) :
    (Nat.card { f : Fin n → Fin n // IsParkingFunction n f ∧
        (∀ i ∈ L, IsLuckyCar f i) ∧
          (∀ i ∈ U, ¬ IsLuckyCar f i) } : ℚ) =
      (∏ i ∈ L, ((n + 1 - i.val : ℕ) : ℚ)) *
        (∏ i ∈ U, (i.val : ℚ)) *
        ((n + 1 : ℚ)) ^ ((n : ℤ) - L.card - U.card - 1)

/-- **Corollary 5**: with `c_k` the number of parking
functions with exactly `k` lucky cars,
`f(x) = ∑_{k} c_k x^k`.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Corollary 5. -/
theorem_wanted luckyGenPoly_eq_sum (n : ℕ) :
    luckyGenPoly n =
      ∑ k ∈ Finset.range (n + 1),
        C ((Nat.card { f : Fin n → Fin n //
          IsParkingFunction n f ∧ luckyCount f = k } : ℕ) : ℚ) *
          X ^ k

/-- **Proposition 6**: the falling-factorial moments of the
lucky-car count `X` for a uniform parking function satisfy
`E[X(X-1)⋯(X-ℓ+1)] = f^{(ℓ)}(1) / (n+1)^{n-1}`, with the
expectation written as the sum over all parking functions
divided by their number `(n+1)^{n-1}`.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Proposition 6. -/
theorem_wanted expected_descFactorial_luckyCount (n ℓ : ℕ)
    (hn : 1 ≤ n) :
    ((∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n =>
        IsParkingFunction n f),
      ((luckyCount f).descFactorial ℓ : ℚ)) /
        (n + 1 : ℚ) ^ (n - 1) =
      (Polynomial.derivative^[ℓ] (luckyGenPoly n)).eval 1 /
        (n + 1 : ℚ) ^ (n - 1))

/-- **Lemma 9**: the boundary values
`q_n(n,j) = \binom{n-1}{j-1} j^{j-2} (n-j+1)^{n-j-1}`,
`q_n(1,j) = ∑_{k=j}^n \binom{n-1}{k-1} k^{k-2} (n-k+1)^{n-k-1}`,
`q_n(i,n) = n^{n-2}`, and
`q_n(i,1) = (n+1)^{n-i-1} n^{i-2} (2n+1-i)`, in zero-based
indices and in `ℚ` for the possibly negative exponents.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 9. -/
theorem_wanted q_boundary_values (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin n) :
    (q n ⟨n - 1, by omega⟩ j : ℚ) =
        Nat.choose (n - 1) j.val * ((j.val + 1 : ℚ)) ^ ((j.val : ℤ) - 1) *
          ((n - j.val : ℚ)) ^ ((n : ℤ) - j.val - 2) ∧
      (q n ⟨0, hn⟩ j : ℚ) =
        ∑ k ∈ Finset.Icc (j.val + 1) n,
          Nat.choose (n - 1) (k - 1) * ((k : ℚ)) ^ ((k : ℤ) - 2) *
            ((n - k + 1 : ℚ)) ^ ((n : ℤ) - k - 1) ∧
      (q n i ⟨n - 1, by omega⟩ : ℚ) = ((n : ℚ)) ^ ((n : ℤ) - 2) ∧
      (q n i ⟨0, hn⟩ : ℚ) =
        ((n + 1 : ℚ)) ^ ((n : ℤ) - i.val - 2) *
          ((n : ℚ)) ^ ((i.val : ℤ) - 1) * (2 * n - i.val)

/-- **Corollary 10**: the number of parking functions in
which the `i`-th car is lucky is
`(n+2-i)(n+1)^{n-2}` (zero-based: `(n+1-i)(n+1)^{n-2}`).

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Corollary 10. -/
theorem_wanted sum_q_eq (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, (q n i j : ℚ)) =
      (n + 1 - i.val : ℚ) * ((n + 1 : ℚ)) ^ ((n : ℤ) - 2)

/-- **Theorem 12**: the number of parking functions in which
the second spot is lucky is
`(3/4)(n+1)^{n-1} - (1/4)(n-1)^{n-1}`.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 12. -/
theorem_wanted sum_q_second_spot (n : ℕ) (hn : 2 ≤ n) :
    (∑ i : Fin n, (q n i ⟨1, hn⟩ : ℚ)) =
      3 / 4 * ((n + 1 : ℚ)) ^ (n - 1) -
        1 / 4 * ((n : ℚ) - 1) ^ (n - 1)

/-- **Lemma 18**: `q_n^i(i,j) = C_{i-1} C_{n-i+1}` if
`i = j` and `0` else (`C` Catalan; zero-based:
`catalan i * catalan (n - i)` on the diagonal).

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 18. -/
theorem_wanted qInc_eq (n : ℕ) (i j : Fin n) :
    qInc n i j =
      if i = j then catalan i.val * catalan (n - i.val)
      else 0

/-- Lattice paths from `(0,0)` to `(k, ℓ)` staying on or
above `y = x`, as step lists (`true` = up, `false` = right)
with `#up ≥ #right` in every prefix. -/
def BallotPath (k ℓ : ℕ) : Type :=
  { w : List Bool // w.length = k + ℓ ∧ w.count true = ℓ ∧
    ∀ m : ℕ, m ≤ w.length →
      (w.take m).count false ≤ (w.take m).count true }

/-- **Lemma 21**: for `ℓ ≥ k`, the number of lattice paths
from `(0,0)` to `(k, ℓ)` staying on or above `y = x` is
`((ℓ-k+1)/(ℓ+1)) \binom{k+ℓ}{k}`.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 21. -/
theorem_wanted card_ballotPath (k ℓ : ℕ) (h : k ≤ ℓ) :
    (Nat.card (BallotPath k ℓ) : ℚ) =
      ((ℓ - k + 1 : ℚ) / (ℓ + 1)) * Nat.choose (k + ℓ) k

/-- **Lemma 22**: `q_n^d(i,j)` in zero-based indices: for
`i + j < n` (the paper's `i + j ≤ n + 1` one-based) it is
the product `((n-i-j)^2 / ((n-i)(n-j))) * C(n-i+j-1, j) *
C(n-j+i-1, i)`, and `0` else.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 22. -/
theorem_wanted qDec_eq (n : ℕ) (i j : Fin n) :
    (qDec n i j : ℚ) =
      if i.val + j.val < n then
        ((n - i.val - j.val : ℚ)) ^ 2 /
            ((n - i.val) * (n - j.val)) *
          Nat.choose (n - i.val + j.val - 1) j.val *
          Nat.choose (n - j.val + i.val - 1) i.val
      else 0

/-- **Corollary 23**: the number of weakly decreasing
parking functions in which spot `j` is lucky (the car
occupying spot `j` is a lucky car), as the sum of the
Lemma 22 values over `i`.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Corollary 23. -/
theorem_wanted card_dec_lucky_spot_eq_sum (n : ℕ) (j : Fin n) :
    (∑ i : Fin n, (qDec n i j : ℚ)) =
      ∑ i ∈ Finset.Icc 1 (n - j.val),
        ((n : ℚ) - i - j.val + 1) ^ 2 /
            ((n + 1 - i) * (n - j.val)) *
          Nat.choose (n - i + j.val) j.val *
          Nat.choose (n - j.val + i - 2) (i - 1)

/-- **Theorem 24**: the number of weakly decreasing parking
functions in which the `j`-th spot is lucky is
`∑_{k=0}^{n-j-1} C_{n-1-k} C_k` (zero-based spot index).

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 24. -/
theorem_wanted card_dec_lucky_spot_eq_sum_catalan (n : ℕ)
    (j : Fin n) :
    (∑ i : Fin n, (qDec n i j : ℚ)) =
      ∑ k ∈ Finset.range (n - j.val),
        ((catalan (n - 1 - k) * catalan k : ℕ) : ℚ)

/-- **Theorem 25**: the expected number of lucky spots for a
weakly decreasing parking function is `(n+1)/2`, with the
expectation written as the sum over all weakly decreasing
parking functions divided by their number `C_n`.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 25. -/
theorem_wanted expected_lucky_dec (n : ℕ) (hn : 1 ≤ n) :
    ((∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n =>
        IsParkingFunction n f ∧ Antitone f),
      (luckyCount f : ℚ)) / (catalan n : ℚ)) =
      ((n : ℚ) + 1) / 2

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
