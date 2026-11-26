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
