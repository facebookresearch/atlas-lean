/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TruncatedLogDiscriminantFinitePrimesIsSquareDiscrTruncatedLog
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import MathlibExt.NumberTheory.TruncatedLogResultantPos

namespace MathlibExtTest.NumberTheory.TruncatedLogDiscriminantFinitePrimesIsSquareDiscrTruncatedLog

open MetaMathlibExt

-- For `m = 3`, only finitely many primes `q` with `3 * q ≡ 1 [MOD 4]` give a square discriminant.
example : {q : ℕ | q.Prime ∧ 3 * q % 4 = 1 ∧
    IsSquare (truncatedLogPolynomial (3 * q)).discr}.Finite :=
  finite_primes_isSquare_discr_truncatedLog (m := 3) (by decide)

-- Hence those primes are bounded.
example : BddAbove {q : ℕ | q.Prime ∧ 3 * q % 4 = 1 ∧
    IsSquare (truncatedLogPolynomial (3 * q)).discr} :=
  (finite_primes_isSquare_discr_truncatedLog (m := 3) (by decide)).bddAbove

-- For `m = 5`, only finitely many primes `q` with `5 * q ≡ 1 [MOD 4]` give a square discriminant.
example : {q : ℕ | q.Prime ∧ 5 * q % 4 = 1 ∧
    IsSquare (truncatedLogPolynomial (5 * q)).discr}.Finite :=
  finite_primes_isSquare_discr_truncatedLog (m := 5) (by decide)

end MathlibExtTest.NumberTheory.TruncatedLogDiscriminantFinitePrimesIsSquareDiscrTruncatedLog
