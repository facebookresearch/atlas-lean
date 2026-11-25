/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.lean`
and
`P2M/Sol/S_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.lean`
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

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Common eigenvectors of commuting endomorphisms

A family of pairwise commuting endomorphisms of a nonzero finite-dimensional
vector space over an algebraically closed field has a common eigenvector. The
proof is by strong induction on the dimension of an invariant subspace: either
every member acts by a scalar, or some member has a proper eigenspace, which is
invariant under the whole family.

## Main results

* `Module.End.exists_forall_apply_eq_smul_of_pairwise_commute`
-/

@[expose] public section

namespace Module.End

open Module Submodule

/-- A family of pairwise commuting endomorphisms of a nonzero finite-dimensional
vector space over an algebraically closed field has a common eigenvector. -/
public theorem exists_forall_apply_eq_smul_of_pairwise_commute
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
  classical
  have hcomm : ∀ i j, Commute (T i) (T j) := by
    intro i j
    rcases eq_or_ne i j with rfl | h
    · exact Commute.refl _
    · exact hT h
  suffices key : ∀ n : ℕ, ∀ W : Submodule K V, finrank K W = n → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, T i w ∈ W) → ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v by
    obtain ⟨v, -, hv0, hv⟩ := key _ ⊤ rfl (by simp) (fun i w _ => mem_top)
    exact ⟨v, hv0, hv⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWn hW0 hWinv
    by_cases hscal : ∀ i, ∃ c : K, ∀ w ∈ W, T i w = c • w
    · obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      refine ⟨v, hvW, hv0, fun i => ?_⟩
      obtain ⟨c, hc⟩ := hscal i
      exact ⟨c, hc v hvW⟩
    · push Not at hscal
      obtain ⟨i₀, hi₀⟩ := hscal
      have hmaps : ∀ w ∈ W, (T i₀) w ∈ W := hWinv i₀
      let S : Module.End K W := (T i₀).restrict hmaps
      have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue S
      let W' : Submodule K V := W ⊓ LinearMap.ker (T i₀ - μ • 1)
      have hW'le : W' ≤ W := inf_le_left
      have hmemW' : ∀ v, v ∈ W' ↔ v ∈ W ∧ T i₀ v = μ • v := by
        intro v
        simp only [W', mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          one_apply_eq_self, sub_eq_zero]
      have hW'0 : W' ≠ ⊥ := by
        obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
        have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
        have hwapp : T i₀ (w : V) = μ • (w : V) := by
          have h2 := congrArg Subtype.val hw.apply_eq_smul
          simpa [S, LinearMap.restrict_apply] using h2
        intro hbot
        have : (w : V) ∈ W' := (hmemW' _).mpr ⟨w.2, hwapp⟩
        rw [hbot, mem_bot] at this
        exact hw0 this
      have hW'ne : W' ≠ W := by
        intro hEq
        obtain ⟨w, hw, hne⟩ := hi₀ μ
        have : w ∈ W' := hEq ▸ hw
        exact hne ((hmemW' w).mp this).2
      have hlt : W' < W := lt_of_le_of_ne hW'le hW'ne
      have hdim : finrank K W' < n := hWn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hW'inv : ∀ i, ∀ w ∈ W', T i w ∈ W' := by
        intro i w hw
        obtain ⟨hwW, hwT⟩ := (hmemW' w).mp hw
        refine (hmemW' _).mpr ⟨hWinv i w hwW, ?_⟩
        calc T i₀ (T i w) = T i (T i₀ w) :=
              congrArg (fun f : Module.End K V => f w) (hcomm i₀ i).eq
          _ = T i (μ • w) := by rw [hwT]
          _ = μ • T i w := by rw [LinearMap.map_smul]
      obtain ⟨v, hvW', hv0, hv⟩ := ih _ hdim W' rfl hW'0 hW'inv
      exact ⟨v, hW'le hvW', hv0, hv⟩

end Module.End
