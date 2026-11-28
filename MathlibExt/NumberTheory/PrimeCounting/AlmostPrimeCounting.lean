/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.AlmostPrime

/-!
# Counting almost primes

The counting function counts positive integers up to a natural cutoff with a fixed number of
prime factors, counted with multiplicity. Its finite-filter characterization uses `(0, x]`.
-/

namespace MetaMathlibExt

attribute [local instance] Classical.propDecidable

@[expose] public section

open Classical in
/-- **Counting almost primes.** For natural numbers $k$ and $x$, $\pi_k(x)$ is the number of
integers $n$ with $1 \le n \le x$ that have exactly $k$ prime factors, counted with multiplicity.
This is the counting function in Landau's theorem on almost primes.

Source: Rafael Jakimczuk, "Functions of Slow Increase and Integer Sequences,"
Journal of Integer Sequences 13 (2010),
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Jakimczuk/jakimczuk8.tex`,
lines 451-453, file SHA256
`b4a7154095398fc4a1729bef9ec80c4005190c1d9ad1dd585fbd2fcdd1eae8d7`, text SHA256
`4af87d665e5485d49e794b3927864d50a1162127411c1427d0f1a379b50b2065`,
module `WantedExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptoticWanted`. -/
noncomputable def almostPrimeCounting (k x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => Nat.IsAlmostPrime k n)).card

/-- The count of `k`-almost primes up to `x` is the cardinality of the filter on `(0, x]`
selecting integers with exactly `k` prime factors, counted with multiplicity. -/
theorem almostPrimeCounting_eq_card_filter (k x : ℕ) :
    almostPrimeCounting k x = ((Finset.Ioc 0 x).filter (Nat.IsAlmostPrime k)).card := by
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := Finset.Icc_succ_left_eq_Ioc 0 x
  rw [almostPrimeCounting, hIcc]

end

end MetaMathlibExt
