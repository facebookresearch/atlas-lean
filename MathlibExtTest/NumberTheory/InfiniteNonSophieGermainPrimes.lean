/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Interval.Finset.Nat
import MathlibExt.NumberTheory.InfiniteNonSophieGermainPrimes

open MetaMathlibExt

-- Above any bound there is a prime whose double plus one is composite.
example (n : ℕ) : ∃ q > n, q.Prime ∧ ¬ (2 * q + 1).Prime := by
  obtain ⟨q, ⟨hq, h⟩, hn⟩ := infinite_setOf_prime_not_isSophieGermainPrime.exists_gt n
  exact ⟨q, hn, hq, fun hp => h ⟨hq, hp⟩⟩
