/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GroupTheory.SimpleGroupPrimeSpectrumSubgroupKourovka11Problem64

open MathlibExt.GroupTheory.SimpleGroupPrimeSpectrumSubgroupKourovka11Problem64Wanted

-- A caller can extract a witness above any requested order bound.
example (N : ℕ) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G),
      IsSimpleGroup G ∧ (∀ n : ℕ, IsEmpty (G ≃* alternatingGroup (Fin n))) ∧
        H ≠ ⊤ ∧ (Nat.card H).primeFactors = (Nat.card G).primeFactors ∧ N < Nat.card G := by
  classical
  by_contra h
  apply finitelyManySimpleWithFullSpectrumSubgroup_refuted
  refine ⟨N, fun G groupG finiteG hsimple hnotalt hsub => ?_⟩
  obtain ⟨H, hproper, hprimes⟩ := hsub
  exact Nat.le_of_not_gt fun hlarge =>
    h ⟨G, groupG, finiteG, H, hsimple, hnotalt, hproper, hprimes, hlarge⟩
