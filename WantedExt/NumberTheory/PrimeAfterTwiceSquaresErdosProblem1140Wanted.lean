/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integers `n` with `n - 2x²` prime for all small `x` (Erdős Problem 1140)

Erdős Problem 1140: do there exist infinitely many `n` such that `n - 2x²` is prime for all `x` with
`2x² < n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeAfterTwiceSquaresErdosProblem1140Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1140, https://www.erdosproblems.com/1140 (status
DISPROVED). UnsolvedMath record UM-30007181 (`EP-1140`), dataset ulamai/UnsolvedMath v1.8.0.

`x` ranges over the integers `x ≥ 0`, so `n` itself must be prime; this matches the known list `2,
5, 7, 13, 31, 61, 181, 199`, which would contain `4` and `15` if `x = 0` were excluded. Compared
with the formal-conjectures statement `ErdosProblems/1140.lean` (equivalent; no code imported).
-/

/-- `n ≥ 1` and `n - 2x²` is prime for every integer `x ≥ 0` with `2x² < n` (`x = 0` makes `n`
itself prime). -/
def AllTwiceSquareShiftsPrime (n : ℕ) : Prop :=
  0 < n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime

/-- Erdős Problem 1140: infinitely many `n` have this property. -/
def infinitelyManyTwiceSquareShiftsPrime : Prop :=
  {n : ℕ | AllTwiceSquareShiftsPrime n}.Infinite

/--
Resolved false: an even such `n` is `2`; Theorem 4.1 of Epure and Gica shows the only such `n ≡ 1
(mod 4)` are `5, 13, 61, 181`, and their method with a result of Mollin and Williams shows the only
such `n ≡ 3 (mod 4)` are `7, 31, 199` and at most one more, so at most nine `n` qualify;
erdosproblems.com/1140 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#1140, https://www.erdosproblems.com/1140 (status DISPROVED); resolution: M. Epure and A. Gica,
Principal quadratic real fields in connection with some additive problems, Bull. Math. Soc. Sci.
Math. Roumanie (N.S.) (2010), 251-259; R. A. Mollin and H. C. Williams, Period four and real
quadratic fields of class number one, Proc. Japan Acad. Ser. A Math. Sci. (1989), 89-93, Epure-Gica
Theorem 4.1 (n ≡ 1 mod 4: only 5, 13, 61, 181) with Mollin-Williams (n ≡ 3 mod 4: only 7, 31, 199
and at most one more); erdosproblems.com/1140.
-/
public theorem_wanted infinitelyManyTwiceSquareShiftsPrime_refuted :
    ¬ infinitelyManyTwiceSquareShiftsPrime

end MathlibExt.NumberTheory.PrimeAfterTwiceSquaresErdosProblem1140Wanted
