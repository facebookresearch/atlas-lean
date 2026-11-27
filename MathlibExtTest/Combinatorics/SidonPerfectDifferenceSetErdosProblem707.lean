/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SidonPerfectDifferenceSetErdosProblem707
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod

open MathlibExt.Combinatorics.SidonPerfectDifferenceSetErdosProblem707Wanted

-- The first three elements already form a perfect difference set at the smallest prime.
example : IsPerfectDifferenceSetMod (↑({1, 2, 4} : Finset ℕ)) 7 := by
  let S : Finset ℕ := {1, 2, 4}
  have h : ∀ r : ZMod 7, r ≠ 0 → ∃! ab : S × S, (ab.1.val : ZMod 7) - ab.2.val = r := by
    unfold ExistsUnique
    decide
  intro r hr
  obtain ⟨⟨a, b⟩, hab, uniq⟩ := h r hr
  refine ⟨(a.val, b.val), ⟨a.property, b.property, hab⟩, ?_⟩
  rintro ⟨c, d⟩ ⟨hc, hd, hcd⟩
  have heq := uniq (⟨c, hc⟩, ⟨d, hd⟩) hcd
  exact congrArg (fun ab : S × S => (ab.1.val, ab.2.val)) heq

-- Although 8 and 1 have the same residue, they give distinct ordered pairs of naturals.
example : ¬ IsPerfectDifferenceSetMod ({1, 2, 4, 8} : Set ℕ) 7 := by
  intro h
  have collision : (2, 1) = (2, 8) :=
    (h 1 (by decide)).unique ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
  contradiction

-- The weak form fails: some finite Sidon set lies in no perfect difference set modulo
-- `m ^ 2 + m + 1`, whatever `m ≥ 1`.
example : ∃ A : Set ℕ, A.Finite ∧ A.IsSidon ∧
    ∀ m : ℕ, 1 ≤ m → ∀ B : Set ℕ, A ⊆ B → ¬ IsPerfectDifferenceSetMod B (m ^ 2 + m + 1) := by
  by_contra h
  apply sidonExtendsToPerfectDifferenceSet_refuted
  intro A hfin hsidon
  by_contra hno
  exact h ⟨A, hfin, hsidon, fun m hm B hAB hB => hno ⟨m, hm, B, hAB, hB⟩⟩

-- Every prime is at least `1`, so refuting the weak form also refutes the prime form.
example : ¬ sidonExtendsToPrimePerfectDifferenceSet := fun h =>
  sidonExtendsToPerfectDifferenceSet_refuted fun A hfin hsidon =>
    let ⟨p, hp, B, hAB, hB⟩ := h A hfin hsidon
    ⟨p, hp.one_lt.le, B, hAB, hB⟩

-- The Sidon set `{1, 2, 4, 8}`, which refutes the prime form, does not refute the weak form: it
-- lies in the perfect difference set of powers of `2` modulo `8 ^ 2 + 8 + 1 = 73`.
example : ∃ B : Set ℕ, {1, 2, 4, 8} ⊆ B ∧ IsPerfectDifferenceSetMod B (8 ^ 2 + 8 + 1) := by
  let S : Finset ℕ := {1, 2, 4, 8, 16, 32, 64, 128, 256}
  have h : ∀ r : ZMod 73, r ≠ 0 → ∃! ab : S × S, (ab.1.val : ZMod 73) - ab.2.val = r := by
    unfold ExistsUnique
    decide +kernel
  refine ⟨S, by simp [S, Set.insert_subset_iff], ?_⟩
  intro r hr
  obtain ⟨⟨a, b⟩, hab, uniq⟩ := h r hr
  refine ⟨(a.val, b.val), ⟨a.property, b.property, hab⟩, ?_⟩
  rintro ⟨c, d⟩ ⟨hc, hd, hcd⟩
  have heq := uniq (⟨c, hc⟩, ⟨d, hd⟩) hcd
  exact congrArg (fun ab : S × S => (ab.1.val, ab.2.val)) heq
