/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SylowMaximalSigmaNilpotentSupplementKourovka19Problem88

open MathlibExt.GroupTheory.KourovkaNotebookShared
open MathlibExt.GroupTheory.SylowMaximalSigmaNilpotentSupplementKourovka19Problem88Wanted

-- In a group of prime order, the whole group supplies a σ-primary supplement.
example {I G : Type} (σ : I → Set ℕ) (hσ : IsPrimePartition σ) [Group G] [Finite G]
    (hG : (Nat.card G).Prime) : IsSigmaNilpotent σ G := by
  apply sylowMaximalSigmaNilpotentSupplement_holds I σ hσ G
  intro p hp P V hV
  refine ⟨⊤, ?_, fun g ↦ ⟨1, V.one_mem, g, Subgroup.mem_top g, one_mul g⟩⟩
  obtain ⟨i, hi⟩ := hσ.2.2 _ hG
  refine ⟨1, fun _ ↦ ⊤, fun _ ↦ ⟨inferInstance, i, ?_⟩, by simp, ?_⟩
  · intro q hq hd
    simp only [Subgroup.card_top] at hd
    exact (Nat.prime_dvd_prime_iff_eq hq hG).mp hd ▸ hi
  · intro k
    have hk : ({k}ᶜ : Set (Fin 1)) = ∅ := by
      ext j
      simp [Subsingleton.elim j k]
    simp [hk]
