/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisShortTranspositionParity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

/-! The off-axis short-coordinate block of the actual axis transposition polynomial.
The proof uses exact short translation, integer pairing, and commutator parity. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

private theorem signed_pair_transposition (a b x y : ℝ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    14 * x - 16 * (8 * x - 8 * a * b * y) +
      (8 * (8 * x - 8 * a * b * y) - 8 * a * b * (8 * y - 8 * a * b * x)) =
      14 * x := by
  have hab : (a * b) ^ 2 = 1 := by rw [mul_pow, ha, hb, one_mul]
  calc
    _ = 14 * x + 64 * ((a * b) ^ 2 - 1) * x := by ring
    _ = 14 * x := by rw [hab]; ring

/-- The rank-axis matrix feedback vanishes in every other short coordinate. -/
theorem conwayShortAxisRaw_product_short_off_axis
    (r u : GriessShortIndex) (c : ZMod 2) (z : ConwayRawSpace) (hur : u ≠ r) :
    (conwayRawProduct (conwayShortAxisRaw r c) z).2.1 u =
      2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 * z.2.1 u -
        8 * qSign c * conwayShortTranslation r z.2.1 u := by
  rw [conwayShortAxisRaw_product_short]
  simp only [Pi.smul_apply, Pi.single_eq_of_ne hur, smul_eq_mul, mul_zero, add_zero]
  ring

/-- The polynomial of the off-axis diagonal/translation block is the actual
commutator sign, even when the intermediate vector has an arbitrary axis coordinate. -/
theorem conwayShort_off_axis_transposition_rows
    (r u : GriessShortIndex) (c : ZMod 2) (X Y : GriessShortIndex → ℝ) (hur : u ≠ r)
    (hY : ∀ v, v ≠ r → Y v =
      2 * stdPairingFun (griessShortVector r) (griessShortVector v) ^ 2 * X v -
        8 * qSign c * conwayShortTranslation r X v) :
    14 * X u - 16 * Y u +
      (2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 * Y u -
        8 * qSign c * conwayShortTranslation r Y u) =
      14 * qSign (conwayAxisShortCommutator r u) * X u := by
  classical
  obtain ⟨n, ⟨hnl, hnh⟩, hn, hcomm⟩ := conwayAxisShort_pairing_cases r u hur
  by_cases hedge : ∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
  · obtain ⟨s, hs⟩ := hedge
    have hsrev := short_product_base_reverse r s u hs
    have hsr : s ≠ r := by
      intro h
      subst s
      exact short_product_self_no_edge r ⟨u, hsrev⟩
    have huD : 2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 = 8 := by
      rcases (short_product_edge_iff_pairing r u).mp ⟨s, hs⟩ with h | h <;>
        rw [h] <;> norm_num
    have hsD : 2 * stdPairingFun (griessShortVector r) (griessShortVector s) ^ 2 = 8 := by
      rcases (short_product_edge_iff_pairing r s).mp ⟨u, hsrev⟩ with h | h <;>
        rw [h] <;> norm_num
    have hsign : qSign (conwayAxisShortCommutator r u) = 1 := by
      rcases (short_product_edge_iff_pairing r u).mp ⟨s, hs⟩ with h | h
      · have he : n = 2 := by exact_mod_cast hn.symm.trans h
        rw [hcomm, he, show ((2 : ℤ) : ZMod 2) = 0 by decide, qSign_zero]
      · have he : n = -2 := by exact_mod_cast hn.symm.trans h
        rw [hcomm, he, show ((-2 : ℤ) : ZMod 2) = 0 by decide, qSign_zero]
    have hyu := hY u hur
    have hys := hY s hsr
    rw [huD, conwayShortTranslation_apply_edge r u s hs] at hyu
    rw [hsD, conwayShortTranslation_apply_edge r s u hsrev,
      short_product_phase_reverse r s u hs] at hys
    rw [huD, conwayShortTranslation_apply_edge r u s hs, hsign, hyu, hys]
    simp only [mul_one]
    simpa only [mul_assoc] using signed_pair_transposition (qSign c)
      (qSign (toAdd (griessShortQ r * griessShortQ s).coeff)) (X u) (X s)
      (by simpa only [pow_two] using qSign_sq c)
      (by simpa only [pow_two] using qSign_sq (toAdd (griessShortQ r * griessShortQ s).coeff))
  · have htX := conwayShortTranslation_apply_no_edge r u hedge X
    have htY := conwayShortTranslation_apply_no_edge r u hedge Y
    have hyu := hY u hur
    rw [htX] at hyu
    have he : ¬ (n = 2 ∨ n = -2) := by
      intro h
      apply hedge
      apply (short_product_edge_iff_pairing r u).mpr
      rcases h with h | h
      · exact Or.inl (by rw [hn, h]; norm_num)
      · exact Or.inr (by rw [hn, h]; norm_num)
    rw [hyu, htY, hn, hcomm]
    interval_cases n <;>
      simp_all [qSign, show ((-1 : ℤ) : ZMod 2) = 1 by decide,
        show ((0 : ℤ) : ZMod 2) = 0 by decide,
        show ((1 : ℤ) : ZMod 2) = 1 by decide] <;> ring

/-- The full raw multiplication polynomial has the required actual sign in every
off-axis short coordinate. No symmetry or spectral hypothesis is required here. -/
theorem conwayShortAxisRaw_transposition_short_off_axis
    (r u : GriessShortIndex) (c : ZMod 2) (z : ConwayRawSpace) (hur : u ≠ r) :
    14 * z.2.1 u - 16 * (conwayRawProduct (conwayShortAxisRaw r c) z).2.1 u +
      (conwayRawProduct (conwayShortAxisRaw r c)
        (conwayRawProduct (conwayShortAxisRaw r c) z)).2.1 u =
      14 * qSign (conwayAxisShortCommutator r u) * z.2.1 u := by
  rw [conwayShortAxisRaw_product_short_off_axis r u c
    (conwayRawProduct (conwayShortAxisRaw r c) z) hur]
  apply conwayShort_off_axis_transposition_rows r u c z.2.1
    (conwayRawProduct (conwayShortAxisRaw r c) z).2.1 hur
  intro v hvr
  exact conwayShortAxisRaw_product_short_off_axis r v c z hvr

/-- The actual local preferred involution acts on short coordinates by this sign;
its central factor changes only the spin constituent. -/
theorem conwayShortAxis_local_short_sign (r u : GriessShortIndex) (c : ZMod 2)
    (X : GriessShortIndex → ℝ) :
    localShortRepresentation (localFiberIncl (qCentral c * griessShortQ r)) X u =
      qSign (conwayAxisShortCommutator r u) * X u := by
  have hp : griessShortPermutation (localFiberIncl (qCentral c * griessShortQ r)).val.2 u = u := by
    change griessShortPermutation 1 u = u
    rw [map_one]
    rfl
  have he := localShortOperator_image (localFiberIncl (qCentral c * griessShortQ r)) X u
  rw [hp] at he
  have hphase : localShortPhase (localFiberIncl (qCentral c * griessShortQ r)) u =
      conwayAxisShortCommutator r u := by
    change toAdd (spinConjugation (spinHolomorphIncl (qCentral c * griessShortQ r))
      (griessShortQ u)).coeff = _
    rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
      griessShortQ_coeff, add_zero, qCentral_mul_base]
    rfl
  rw [hphase] at he
  exact he

/-- Off-axis form with the actual local action as the right-hand side. -/
theorem conwayShortAxisRaw_transposition_short_off_axis_local
    (r u : GriessShortIndex) (c : ZMod 2) (z : ConwayRawSpace) (hur : u ≠ r) :
    14 * localShortRepresentation (localFiberIncl (qCentral c * griessShortQ r)) z.2.1 u =
      14 * z.2.1 u - 16 * (conwayRawProduct (conwayShortAxisRaw r c) z).2.1 u +
      (conwayRawProduct (conwayShortAxisRaw r c)
        (conwayRawProduct (conwayShortAxisRaw r c) z)).2.1 u := by
  rw [conwayShortAxis_local_short_sign]
  simpa only [mul_assoc] using (conwayShortAxisRaw_transposition_short_off_axis r u c z hur).symm

/-- Every scalar rank-axis correction vanishes in off-axis short coordinates. -/
theorem conwayShortAxisRaw_rank_correction_off_axis
    (r u : GriessShortIndex) (c : ZMod 2) (a : ℝ) (hur : u ≠ r) :
    (a • conwayShortAxisRaw r c).2.1 u = 0 := by
  classical
  simp [conwayShortAxisRaw, Pi.single_eq_of_ne hur]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
