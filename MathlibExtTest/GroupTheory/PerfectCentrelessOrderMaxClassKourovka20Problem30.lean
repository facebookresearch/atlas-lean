/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PerfectCentrelessOrderMaxClassKourovka20Problem30
import Mathlib.Algebra.Group.PUnit
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Push

open MathlibExt.GroupTheory.PerfectCentrelessOrderMaxClassKourovka20Problem30Wanted

-- Recover a single group where the bound fails strictly for every centralizer index.
example : ∃ (G : Type) (_ : Group G), Finite G ∧ Group.IsPerfect G ∧
    Subgroup.center G = ⊥ ∧ ∀ x : G, (Subgroup.centralizer {x}).index ^ 2 < Nat.card G := by
  have h := perfectCentrelessOrderLeMaxClassSq_refuted
  unfold perfectCentrelessOrderLeMaxClassSq at h
  push Not at h
  simpa only [Subgroup.index_centralizer_eq_ncard] using h

-- The identity class attains equality in the trivial group.
example : Nat.card PUnit = (conjugatesOf (1 : PUnit)).ncard ^ 2 := by
  have h : conjugatesOf (1 : PUnit) = {1} := by ext; simp [conjugatesOf]
  rw [h, Set.ncard_singleton, one_pow]
  simp
