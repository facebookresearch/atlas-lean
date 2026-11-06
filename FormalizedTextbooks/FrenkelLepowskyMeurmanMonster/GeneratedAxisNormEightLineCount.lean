/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCount

/-! Counting actual unoriented norm-eight lines through their two physical orientations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Forget orientation, retaining the genuine physical outer matrix. -/
def generatedNormEightLine : LeechNormEight → GeneratedNormEightLines :=
  fun u => ⟨generatedNormEightLineMatrix u, ⟨u, rfl⟩⟩

theorem generatedNormEightLine_surjective : Function.Surjective generatedNormEightLine := by
  rintro ⟨P, u, hu⟩
  exact ⟨u, Subtype.ext hu⟩

instance : Finite GeneratedNormEightLines :=
  Finite.of_surjective generatedNormEightLine generatedNormEightLine_surjective

/-- Exactly two actual lattice vectors represent each genuine physical line. -/
theorem generatedNormEightLine_fiber_card (P : GeneratedNormEightLines) :
    Nat.card {u : LeechNormEight // generatedNormEightLine u = P} = 2 := by
  classical
  obtain ⟨u, hu⟩ := generatedNormEightLine_surjective P
  let f : Bool → {v : LeechNormEight // generatedNormEightLine v = P} := fun b =>
    ⟨if b then generatedNormEightNeg u else u, by
      cases b
      · exact hu
      · exact (Subtype.ext (generatedNormEightLineMatrix_neg u)).trans hu⟩
  have hf : Function.Injective f := by
    intro a b h
    have he := congrArg Subtype.val h
    cases a <;> cases b
    · rfl
    · exact False.elim (generatedNormEightNeg_ne u he.symm)
    · exact False.elim (generatedNormEightNeg_ne u he)
    · rfl
  have hs : Function.Surjective f := by
    rintro ⟨v, hv⟩
    have he : generatedNormEightLineMatrix u = generatedNormEightLineMatrix v :=
      congrArg Subtype.val (hu.trans hv.symm)
    rcases (generatedNormEightLineMatrix_eq_iff u v).mp he with h | h
    · exact ⟨false, Subtype.ext h.symm⟩
    · exact ⟨true, Subtype.ext h.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)]
  simp [Nat.card_eq_fintype_card]

/-- The actual 398034000 norm-eight vectors give 199017000 unoriented lines. -/
theorem generatedNormEightLines_card : Nat.card GeneratedNormEightLines = 199017000 := by
  let : Fintype GeneratedNormEightLines := Fintype.ofFinite GeneratedNormEightLines
  have h : 398034000 = Nat.card GeneratedNormEightLines * 2 := by
    calc
      398034000 = Nat.card LeechNormEight := leechNormEight_card.symm
      _ = Nat.card (Σ P : GeneratedNormEightLines,
          {u : LeechNormEight // generatedNormEightLine u = P}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv generatedNormEightLine).symm
      _ = ∑ P : GeneratedNormEightLines,
          Nat.card {u : LeechNormEight // generatedNormEightLine u = P} := Nat.card_sigma
      _ = ∑ _P : GeneratedNormEightLines, 2 :=
        Finset.sum_congr rfl (fun P _ => generatedNormEightLine_fiber_card P)
      _ = Nat.card GeneratedNormEightLines * 2 := by simp [Nat.card_eq_fintype_card]
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
