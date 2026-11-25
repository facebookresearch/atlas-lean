/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RestrictedSignedSumsetAPOneExtra

open MetaMathlibExt

private theorem indexedAP_four (b d : ℤ) (hd : 0 < d) :
    IsIndexedAP (fun i : Fin (3 + 1) => b + (i : ℤ) * d) d := by
  refine ⟨hd, ?_⟩
  intro i j hij
  have h : (j.val : ℤ) = (i.val : ℤ) + 1 := by exact_mod_cast hij.symm
  change b + (j.val : ℤ) * d = b + (i.val : ℤ) * d + d
  rw [h, add_mul, one_mul, add_assoc]

-- The least permitted number of summands attains the quadratic bound for the odd progression.
example : (restrictedSignedSumset 3
    (orderedFinset (fun i : Fin (3 + 1) => 1 + (i : ℤ) * 2))).card = 16 := by
  let a : Fin (3 + 1) → ℤ := fun i => 1 + (i : ℤ) * 2
  have ha : StrictMono a := by
    intro i j hij
    have hv : (i.val : ℤ) < (j.val : ℤ) := by exact_mod_cast (show i.val < j.val from hij)
    change 1 + (i.val : ℤ) * 2 < 1 + (j.val : ℤ) * 2
    omega
  have hp (i : Fin (3 + 1)) : 0 < a i := by dsimp [a]; omega
  have he := (card_restrictedSignedSumset_ap_h_add_one 3 (by decide) a 2 ha hp
    (indexedAP_four 1 2 (by decide))).2.mpr (by decide)
  exact_mod_cast he

-- A different step uses the strengthened branch and cannot attain the quadratic bound.
example : let c := (restrictedSignedSumset 3
    (orderedFinset (fun i : Fin (3 + 1) => 1 + (i : ℤ)))).card; 17 ≤ c ∧ c ≠ 16 := by
  let a : Fin (3 + 1) → ℤ := fun i => 1 + (i : ℤ)
  have ha : StrictMono a := by
    intro i j hij
    have hv : (i.val : ℤ) < (j.val : ℤ) := by exact_mod_cast (show i.val < j.val from hij)
    change 1 + (i.val : ℤ) < 1 + (j.val : ℤ)
    omega
  have hp (i : Fin (3 + 1)) : 0 < a i := by dsimp [a]; omega
  have hap : IsIndexedAP a 1 := by simpa [a] using indexedAP_four 1 1 (by decide)
  obtain ⟨hbound, heq⟩ := card_restrictedSignedSumset_ap_h_add_one 3 (by decide) a 1 ha hp hap
  have hl : (17 : ℤ) ≤ ((restrictedSignedSumset 3 (orderedFinset a)).card : ℤ) := by
    simpa [show 1 ≠ 2 * a 0 by decide] using hbound
  refine ⟨by exact_mod_cast hl, ?_⟩
  intro hc
  exact (show (1 : ℤ) ≠ 2 * a 0 by decide) (heq.mp (by exact_mod_cast hc))
