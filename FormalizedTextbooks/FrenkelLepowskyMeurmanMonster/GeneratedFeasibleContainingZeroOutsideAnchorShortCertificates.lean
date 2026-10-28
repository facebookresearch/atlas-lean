/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorOctadRow13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorPairPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorPairPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorPairPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorPairPacket03

/-! Complete sparse source and Fourier certificates assembled without omitted coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All14 actual encoder rows and all64 preferred signs retain both full sparse stages. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadQ_literal (t : Fin 2) (j : Fin 14) (e : Fin 64) :
    generatedFeasibleContainingZeroOutsideAnchorOctadQ (if t = 0 then 1 else 2) (generatedFeasibleContainingZeroOutsideAnchorCode j) e =
      generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ t j e := by
  fin_cases j
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow00_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow01_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow02_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow03_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow04_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow05_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow06_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow07_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow08_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow09_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow10_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow11_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow12_sparse t e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow13_sparse t e

/-- Every actual cached code row satisfies the entire original64-by64 Fourier equation. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadQ_fourier (j : Fin 14) (e : Fin 64) :
    (∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 *
      generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ 0 j f) = generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ 1 j e := by
  fin_cases j
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow00_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow01_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow02_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow03_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow04_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow05_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow06_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow07_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow08_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow09_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow10_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow11_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow12_fourier e
  · exact generatedFeasibleContainingZeroOutsideAnchorOctadRow13_fourier e

private theorem pair_address (p : Fin 276) :
    ∃ k : Fin 4, ∃ q : Fin 69, generatedFeasibleContainingZeroOutsideAnchorPairPacketIndex k q = p := by
  let k : Fin 4 := ⟨p.val / 69, by omega⟩
  let q : Fin 69 := ⟨p.val % 69, Nat.mod_lt _ (by decide)⟩
  exact ⟨k, q, Fin.ext (by dsimp [generatedFeasibleContainingZeroOutsideAnchorPairPacketIndex, k, q]; omega)⟩

/-- Both actual preferred signs of every one of the276 physical pairs are bound to the whole sum. -/
theorem generatedFeasibleContainingZeroOutsideAnchorPairQ_literal (t : Fin 2) (s : Fin 2) (p : Fin 276) :
    generatedFeasibleContainingZeroOutsideAnchorPairQ (if t = 0 then 1 else 2) s p = generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ t s p := by
  obtain ⟨k, q, hq⟩ := pair_address p
  rw [← hq]
  fin_cases k
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket00_sparse t s q
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket01_sparse t s q
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket02_sparse t s q
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket03_sparse t s q

/-- All552 preferred pair outputs obey the complete original triality equation. -/
theorem generatedFeasibleContainingZeroOutsideAnchorPairQ_triality (s : Fin 2) (p : Fin 276) :
    let m := generatedFeasibleContainingZeroOutsideAnchorMatrix1Q (generatedAxisGlobalPairCoordinates p).1
      (generatedAxisGlobalPairCoordinates p).2
    let b := (generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 0 0 p - generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 0 1 p) / 2
    (if s = 0 then m + b else b - m) = generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 1 s p := by
  obtain ⟨k, q, hq⟩ := pair_address p
  rw [← hq]
  fin_cases k
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket00_triality s q
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket01_triality s q
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket02_triality s q
  · exact generatedFeasibleContainingZeroOutsideAnchorPairPacket03_triality s q

/-- Every encoder row outside the full realized support is zero at every stage and sign. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadQ_zero_outside (k : Fin 4) (d : Fin 4096) (e : Fin 64)
    (hd : ∀ j : Fin 14, d ≠ generatedFeasibleContainingZeroOutsideAnchorCode j) : generatedFeasibleContainingZeroOutsideAnchorOctadQ k d e = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  cases h : generatedFeasibleContainingZeroOutsideAnchorRoot k n with
  | inl z => simp [h]
  | inr z =>
    rcases z with ⟨j, f⟩
    simp [h, hd j]

/-- The first intermediate pair stage is its full literal packet. -/
theorem generatedFeasibleContainingZeroOutsideAnchorPairQ_one (s : Fin 2) (p : Fin 276) :
    generatedFeasibleContainingZeroOutsideAnchorPairQ 1 s p =
      generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 0 s p :=
  generatedFeasibleContainingZeroOutsideAnchorPairQ_literal 0 s p

/-- The forward-triality pair stage is its full literal packet. -/
theorem generatedFeasibleContainingZeroOutsideAnchorPairQ_two (s : Fin 2) (p : Fin 276) :
    generatedFeasibleContainingZeroOutsideAnchorPairQ 2 s p =
      generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 1 s p :=
  generatedFeasibleContainingZeroOutsideAnchorPairQ_literal 1 s p

/-- The first intermediate octad stage is its full literal packet on every cached code. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadQ_one (j : Fin 14) (e : Fin 64) :
    generatedFeasibleContainingZeroOutsideAnchorOctadQ 1
        (generatedFeasibleContainingZeroOutsideAnchorCode j) e =
      generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ 0 j e :=
  generatedFeasibleContainingZeroOutsideAnchorOctadQ_literal 0 j e

/-- The forward-triality octad stage is its full literal packet on every cached code. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadQ_two (j : Fin 14) (e : Fin 64) :
    generatedFeasibleContainingZeroOutsideAnchorOctadQ 2
        (generatedFeasibleContainingZeroOutsideAnchorCode j) e =
      generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ 1 j e :=
  generatedFeasibleContainingZeroOutsideAnchorOctadQ_literal 1 j e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
