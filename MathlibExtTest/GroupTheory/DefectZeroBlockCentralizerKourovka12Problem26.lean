/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic

open MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26Wanted

namespace MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26Wanted.Test

private theorem exactStatement :
    ¬∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPSoluble p G →
      (HasDefectZeroBlock p G ↔
        ∃ N : Subgroup G, N.Normal ∧ (Nat.card N).Coprime p ∧
          ∃ x ∈ N, (Nat.card (Subgroup.centralizer {x})).Coprime p) :=
  defectZeroBlockIffPRegularCentralizer_refuted

private lemma soluble_single_factor {G : Type} [Group G]
    (h : Nat.card G = 2 ∨ (Nat.card G).Coprime 2) : IsPSoluble 2 G := by
  refine ⟨1, ![⊥, ⊤], rfl, rfl, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let K := (⊥ : Subgroup G).subgroupOf ⊤
  have hcard : Nat.card ((⊤ : Subgroup G) ⧸ K) = Nat.card G := by
    rw [show K = ⊥ by simp [K],
      Nat.card_congr (QuotientGroup.quotientBot (G := ↥(⊤ : Subgroup G))).toEquiv,
      Subgroup.card_top]
  change (⊥ : Subgroup G) ≤ ⊤ ∧ ∃ _ : K.Normal,
    IsPGroup 2 ((⊤ : Subgroup G) ⧸ K) ∨ (Nat.card ((⊤ : Subgroup G) ⧸ K)).Coprime 2
  refine ⟨bot_le, inferInstance, ?_⟩
  rcases h with h | h
  · exact Or.inl (IsPGroup.of_card (n := 1) (hcard.trans (h.trans (pow_one 2).symm)))
  · exact Or.inr (hcard.symm ▸ h)

-- The single factor is a 2-group for C₂ and has odd order for C₃.
example : IsPSoluble 2 (Multiplicative (ZMod 2)) :=
  soluble_single_factor (Or.inl (Nat.card_zmod 2))

example : IsPSoluble 2 (Multiplicative (ZMod 3)) :=
  soluble_single_factor (Or.inr ((Nat.card_zmod 3).symm ▸ (by decide : Nat.Coprime 3 2)))

-- Every irreducible complex representation of C₂ has degree one.
example : ¬HasDefectZeroBlock 2 (Multiplicative (ZMod 2)) := by
  rintro ⟨V, _, _, _, ρ, hρ, hd⟩
  have : ρ.IsIrreducible := hρ
  have hdim := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  rw [hcard, Nat.prime_two.factorization, Finsupp.single_eq_same, pow_one, hdim] at hd
  exact (by decide : ¬(2 : ℕ) ∣ 1) hd

end MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26Wanted.Test
