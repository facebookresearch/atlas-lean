/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsGreedy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsLabels

/-! A sixteen-element binary subspace contains a nonzero vector with its three
highest coordinates zero. Its least nonzero numerical label is therefore below32. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Vanishing highest coordinates bound the little-endian label by31. -/
theorem generatedAxisE8FrameLabel_lt_thirty_two
    (v : Fin 8 → ZMod 2) (h5 : v 5 = 0) (h6 : v 6 = 0) (h7 : v 7 = 0) :
    (generatedAxisE8FrameLabel v).val < 32 := by
  have hv (i : Fin 8) : (v i).val ≤ 1 := by have := (v i).val_lt; omega
  change (∑ i : Fin 8, (v i).val * 2 ^ i.val) % 256 < 32
  have hs : (∑ i : Fin 8, (v i).val * 2 ^ i.val) < 32 := by
    norm_num [Fin.sum_univ_succ, h5, h6, h7]
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    have h3 := hv 3
    have h4 := hv 4
    omega
  exact (Nat.mod_le _ _).trans_lt hs

/-- Pigeonhole on the three high bits supplies a nonzero vector labelled below32. -/
theorem generatedAxisE8Frame_subspace_small_label
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (hW : Nat.card W = 16) :
    ∃ v ∈ W, v ≠ 0 ∧ (generatedAxisE8FrameLabel v).val < 32 := by
  let f : W → (Fin 3 → ZMod 2) := fun v i => v.val ⟨i.val + 5, by omega⟩
  have hc : Nat.card (Fin 3 → ZMod 2) = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hn : ¬ Function.Injective f := by
    intro hi
    have h := Nat.card_le_card_of_injective f hi
    rw [hW, hc] at h
    omega
  simp only [Function.Injective] at hn
  push Not at hn
  obtain ⟨u, v, he, hne⟩ := hn
  let w := u.val - v.val
  have hw0 : w ≠ 0 := by
    intro h
    exact hne (Subtype.ext (sub_eq_zero.mp h))
  have hh (i : Fin 3) : w ⟨i.val + 5, by omega⟩ = 0 :=
    sub_eq_zero.mpr (congrFun he i)
  refine ⟨w, W.sub_mem u.property v.property, hw0, ?_⟩
  exact generatedAxisE8FrameLabel_lt_thirty_two w (hh 0) (hh 1) (hh 2)

/-- The first vector of a genuine greedy four-basis has numerical label below32. -/
theorem generatedAxisE8FrameGreedy_first_label
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (hW : Nat.card W = 16)
    (a b c d : Fin 8 → ZMod 2)
    (hg : generatedAxisE8FrameGreedyIn W [a, b, c, d]) :
    (generatedAxisE8FrameLabel a).val < 32 := by
  obtain ⟨v, hv, hv0, hlabel⟩ := generatedAxisE8Frame_subspace_small_label W hW
  have hm := (hg.2 (0 : Fin 4)).2 v hv
  have hn : v ∉ generatedAxisE8FrameListSpan ([a, b, c, d].take 0) := by
    simpa [generatedAxisE8FrameListSpan] using hv0
  have hle : (generatedAxisE8FrameLabel a).val ≤ (generatedAxisE8FrameLabel v).val := hm hn
  exact hle.trans_lt hlabel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
