/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219

/-! # Tests for Shelah's partition relation -/

namespace MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted.Test

open Cardinal

private abbrev Summand (n : ℕ → ℕ) (i : ℕ) : Type := ((2 : Cardinal.{0}) ^ ℵ_ (n i)).out

-- Colour a pair by whether its two points lie in the same summand.
-- A homogeneous set in the other colour would inject into ℕ.
example (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun i => (2 : Cardinal.{0}) ^ ℵ_ (n i))
    (hfirst : ℵ_ Ordinal.omega0 < (2 : Cardinal.{0}) ^ ℵ_ (n 0)) :
    ∃ H : Set (Σ i : ℕ, Summand n i), #H = ℵ_ Ordinal.omega0 ∧
      ∀ x ∈ H, ∀ y ∈ H, x.1 = y.1 := by
  let c (x y : Σ i : ℕ, Summand n i) : Bool := decide (x.1 = y.1)
  have hc (x y) : c x y = c y x := by simp [c, eq_comm]
  have hsum :
      #(Σ i : ℕ, Summand n i) = Cardinal.sum (fun i => (2 : Cardinal.{0}) ^ ℵ_ (n i)) := by
    simp only [mk_sigma, Summand, mk_out]
  obtain ⟨H, hH, b, hmono⟩ :=
    alephOmegaPartitionOfCardinalSum_holds n hn hpow hfirst _ hsum c hc
  refine ⟨H, hH, ?_⟩
  cases b with
  | true =>
    intro x hx y hy
    by_cases h : x = y
    · exact congrArg Sigma.fst h
    · simpa [c] using hmono x hx y hy h
  | false =>
    exfalso
    have hinj : Function.Injective (fun x : H => x.val.1) := by
      intro x y he
      by_contra hne
      have hh := hmono x.val x.property y.val y.property (fun h => hne (Subtype.ext h))
      simp [c, he] at hh
    have hle := mk_le_of_injective hinj
    rw [hH, mk_nat] at hle
    exact (aleph0_lt_aleph.mpr Ordinal.omega0_pos).not_ge hle

end MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted.Test
