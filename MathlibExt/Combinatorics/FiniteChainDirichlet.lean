/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet.lean`
and
`P2M/Sol/S_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Data.Nat.Init
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

namespace ModularCurve
namespace ChainDirichlet

private def chainRec (r : ℕ → ℤ) (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => t
  | (d + 2) => 2 * chainRec r t (d + 1) - chainRec r t d - r (d + 1)

private theorem chainRec_zero (r : ℕ → ℤ) (t : ℤ) : chainRec r t 0 = 0 := rfl

private theorem chainRec_one (r : ℕ → ℤ) (t : ℤ) : chainRec r t 1 = t := rfl

private theorem chainRec_succ_succ (r : ℕ → ℤ) (t : ℤ) (d : ℕ) :
    chainRec r t (d + 2) = 2 * chainRec r t (d + 1) - chainRec r t d - r (d + 1) := rfl

private theorem chainRec_laplace (r : ℕ → ℤ) (t : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    chainRec r t (d - 1) - 2 * chainRec r t d + chainRec r t (d + 1) = -r d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, show e + 1 + 1 = e + 2 from rfl, chainRec_succ_succ]
  ring

private theorem chainRec_eq (r : ℕ → ℤ) (t : ℤ) (d : ℕ) :
    chainRec r t d = d * t + chainRec r 0 d := by
  induction d using Nat.twoStepInduction with
  | zero => simp [chainRec_zero]
  | one => simp [chainRec_one]
  | more d ih0 ih1 =>
    rw [chainRec_succ_succ, chainRec_succ_succ, ih0, ih1]
    push_cast
    ring

private def corr (r : ℕ → ℤ) (ν : ℤ) : ℕ → ℤ := fun d => if d = 1 then r d - ν else r d

private theorem chainRec_corr (r : ℕ → ℤ) (ν : ℤ) (d : ℕ) :
    chainRec (corr r ν) 0 d = chainRec r 0 d + ((d - 1 : ℕ) : ℤ) * ν := by
  induction d using Nat.twoStepInduction with
  | zero => simp [chainRec_zero]
  | one => simp [chainRec_one]
  | more d ih0 ih1 =>
    rw [chainRec_succ_succ, chainRec_succ_succ, ih0, ih1]
    rcases Nat.eq_zero_or_pos d with rfl | hdp
    · simp [chainRec_zero, chainRec_one, corr]; ring
    · have hc : corr r ν (d + 1) = r (d + 1) := by
        unfold corr; rw [if_neg (by omega)]
      rw [hc]
      have h1 : ((d + 1 - 1 : ℕ) : ℤ) = d := by omega
      have h2 : ((d - 1 : ℕ) : ℤ) = d - 1 := by omega
      have h3 : ((d + 2 - 1 : ℕ) : ℤ) = d + 1 := by omega
      rw [h1, h2, h3]
      ring

private theorem chainRec_corr_self_eq_zero (r : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    chainRec (corr r (chainRec r 0 n)) (-(chainRec r 0 n)) n = 0 := by
  rw [chainRec_eq, chainRec_corr]
  have hnn : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [hnn]; ring

/-- An integral Dirichlet equation on finitely many finite chains can be
solved after a correction at the first interior vertex of each chain.

For each chain `i` of length `n i ≥ 1` and integers `r i d`, there are integers
`ν i` and `c i d`, vanishing at and beyond the endpoints, whose discrete
Laplacian `c (d-1) - 2 c d + c (d+1)` equals `-(r d - ν)` at `d = 1` and
`-r d` at every other interior vertex. Chains of length one need no
correction. -/
public theorem exists_depthOne_correction_dirichlet {ι : Type*} (n : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) (r : ι → ℕ → ℤ) :
    ∃ (ν : ι → ℤ) (c : ι → ℕ → ℤ),
      (∀ i, n i = 1 → ν i = 0) ∧ (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = 0) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i →
        c i (d - 1) - 2 * c i d + c i (d + 1) = -(if d = 1 then r i d - ν i else r i d) := by
  classical
  let ν : ι → ℤ := fun i => if n i = 1 then 0 else chainRec (r i) 0 (n i)
  let c : ι → ℕ → ℤ := fun i d => if n i ≤ d then 0
    else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d
  refine ⟨ν, c, ?_, ?_, ?_, ?_⟩
  · intro i hi
    show (if n i = 1 then (0 : ℤ) else chainRec (r i) 0 (n i)) = 0
    rw [if_pos hi]
  · intro i
    have hni : ¬ n i ≤ 0 := by have := hn i; omega
    show (if n i ≤ 0 then (0 : ℤ)
      else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) 0) = 0
    rw [if_neg hni, chainRec_zero]
  · intro i d hd
    show (if n i ≤ d then (0 : ℤ)
      else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d) = 0
    rw [if_pos hd]
  · intro i d hd1 hd2
    have hni : ¬ n i = 1 := by omega
    have hνi : ν i = chainRec (r i) 0 (n i) := by
      show (if n i = 1 then (0 : ℤ) else chainRec (r i) 0 (n i)) = _
      rw [if_neg hni]
    have hc : ∀ e, c i e = if n i ≤ e then 0
        else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) e := fun e => rfl
    have hcorr : corr (r i) (ν i) d = (if d = 1 then r i d - ν i else r i d) := rfl
    have key := chainRec_laplace (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d hd1
    have hend : chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) (n i) = 0 := by
      rw [hνi]; exact chainRec_corr_self_eq_zero (r i) (n i) (hn i)
    rw [hc (d - 1), hc d, hc (d + 1), if_neg (by omega), if_neg (by omega), ← hcorr]
    by_cases h2 : n i ≤ d + 1
    · have heq : d + 1 = n i := by omega
      rw [if_pos h2, ← key, heq, hend]
    · rw [if_neg h2, ← key]

end ChainDirichlet
end ModularCurve
