/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSetIsArithmeticalCompactSetDerivedSetIterate

namespace MathlibExtTest.Topology.ArithmeticalSelfSimilarCompactSetIsArithmeticalCompactSetDerivedSetIterate

open MetaMathlibExt

-- The first derived set of an arithmetical compact set is arithmetical.
example {K : Set ℝ} {μ ρ : ℕ} (hK : IsArithmeticalCompactSet K μ ρ) :
    IsArithmeticalCompactSet (derivedSet K) μ ρ := by
  have h := isArithmeticalCompactSet_derivedSet_iterate hK 1
  simpa only [Function.iterate_one] using h

-- Iterated derived sets compose: the (m + n)-th derived set is arithmetical.
example {K : Set ℝ} {μ ρ : ℕ} (hK : IsArithmeticalCompactSet K μ ρ) (m n : ℕ) :
    IsArithmeticalCompactSet (derivedSet^[m + n] K) μ ρ := by
  rw [Function.iterate_add_apply]
  exact isArithmeticalCompactSet_derivedSet_iterate
    (isArithmeticalCompactSet_derivedSet_iterate hK n) m

-- Derived sets of arithmetical compact sets are quasi-arithmetical.
example {K : Set ℝ} {μ ρ : ℕ} (hK : IsArithmeticalCompactSet K μ ρ) (n : ℕ) :
    IsQuasiArithmeticalCompactSet (derivedSet^[n] K) μ ρ :=
  (isArithmeticalCompactSet_derivedSet_iterate hK n).isQuasiArithmeticalCompactSet

end MathlibExtTest.Topology.ArithmeticalSelfSimilarCompactSetIsArithmeticalCompactSetDerivedSetIterate
