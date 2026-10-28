/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsLabels

/-! Ordinary binary subspace growth and minimum-label choice for greedy frame bases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Adjoining an independent binary vector doubles the genuine subspace cardinality. -/
theorem generatedAxisE8Frame_subspace_adjoin_card
    (S : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (v : Fin 8 → ZMod 2) (hv : v ∉ S) :
    Nat.card ↥(S ⊔ Submodule.span (ZMod 2) {v}) = 2 * Nat.card S := by
  classical
  let f : S × ZMod 2 → ↥(S ⊔ Submodule.span (ZMod 2) {v}) := fun x =>
    ⟨x.1.val + x.2 • v, Submodule.add_mem _
      ((show S ≤ S ⊔ Submodule.span (ZMod 2) {v} from le_sup_left) x.1.property)
      ((show Submodule.span (ZMod 2) {v} ≤ S ⊔ Submodule.span (ZMod 2) {v} from le_sup_right)
        (Submodule.smul_mem _ x.2 (Submodule.subset_span (by simp))))⟩
  have htwo : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  have hinj : Function.Injective f := by
    rintro ⟨s, c⟩ ⟨t, d⟩ he
    have hval := congrArg Subtype.val he
    change s.val + c • v = t.val + d • v at hval
    rcases htwo c with hc | hc <;> rcases htwo d with hd | hd
    · have hs : s = t := Subtype.ext (by simpa [hc, hd] using hval)
      exact Prod.ext hs (hc.trans hd.symm)
    · have hs : s.val = t.val + v := by simpa [hc, hd] using hval
      have he : v = s.val - t.val := (eq_sub_iff_add_eq).mpr (by
        simpa only [add_comm] using hs.symm)
      exact (hv (he ▸ S.sub_mem s.property t.property)).elim
    · have hs : s.val + v = t.val := by simpa [hc, hd] using hval
      have he : v = t.val - s.val := (eq_sub_iff_add_eq).mpr (by
        simpa only [add_comm] using hs)
      exact (hv (he ▸ S.sub_mem t.property s.property)).elim
    · have hs : s = t := Subtype.ext (by simpa [hc, hd] using hval)
      exact Prod.ext hs (hc.trans hd.symm)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨s, hs, t, ht, he⟩ := Submodule.mem_sup.mp x.property
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ht
    refine ⟨(⟨s, hs⟩, c), Subtype.ext ?_⟩
    change s + c • v = x.val
    rwa [hc]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod]
  have hc : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [hc, mul_comm]

/-- A proper subspace of a sixteen-element space has a least-label vector outside it. -/
theorem generatedAxisE8Frame_minimum_outside
    (W S : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hSW : S ≤ W) (hc : Nat.card S < Nat.card W) :
    ∃ v : Fin 8 → ZMod 2, v ∈ W ∧ v ∉ S ∧
      ∀ w ∈ W, w ∉ S → generatedAxisE8FrameLabel v ≤ generatedAxisE8FrameLabel w := by
  classical
  have hex : ∃ v, v ∈ W ∧ v ∉ S := by
    by_contra hn
    push Not at hn
    have he : W = S := le_antisymm (fun v hv => hn v hv) hSW
    rw [he] at hc
    exact (lt_irrefl _ hc)
  let T : Finset (Fin 256) := Finset.univ.filter (fun a =>
    generatedAxisE8FrameLabelBits a ∈ W ∧ generatedAxisE8FrameLabelBits a ∉ S)
  have hT : T.Nonempty := by
    obtain ⟨v, hv, hs⟩ := hex
    refine ⟨generatedAxisE8FrameLabel v, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [generatedAxisE8FrameLabel_right v]
    exact ⟨hv, hs⟩
  let a := T.min' hT
  have ha : generatedAxisE8FrameLabelBits a ∈ W ∧ generatedAxisE8FrameLabelBits a ∉ S :=
    (Finset.mem_filter.mp (T.min'_mem hT)).2
  refine ⟨generatedAxisE8FrameLabelBits a, ha.1, ha.2, ?_⟩
  intro w hw hs
  have hm : generatedAxisE8FrameLabel w ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [generatedAxisE8FrameLabel_right w]
    exact ⟨hw, hs⟩
  rw [generatedAxisE8FrameLabel_left a]
  exact T.min'_le _ hm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
