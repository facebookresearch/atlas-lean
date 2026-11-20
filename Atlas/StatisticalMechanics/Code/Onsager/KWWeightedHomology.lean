/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeighted
import Code.Onsager.TorusLoopHomology










namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_spinPhase_product_eq_homology
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (d k).2) =
      ons_spinLinearCharacter a b
        (ons_evenHomology L (ons_dartEdgeSet d)) := by
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists d hvalid
  rw [prod_ons_dirPhase _ _ (ons_spinPhase_ne_zero L a)
    (ons_spinPhase_ne_zero L b) (fun k => (d k).2), hmx, hmy]
  have ha : ons_spinPhase L a ^ (L : ℤ) = (-1 : ℂ) ^ (a.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hb : ons_spinPhase L b ^ (L : ℤ) = (-1 : ℂ) ^ (b.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  rw [_root_.zpow_mul, _root_.zpow_mul, ha, hb,
    ← _root_.zpow_mul, ← _root_.zpow_mul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ons_spinPhase_character]
  rw [ons_evenHomology_dartEdgeSet_eq_windingParity
    d hvalid hsite hnu mx my hmx hmy]

theorem ons_loopWeight_weightedPhase_eq_homology
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      ons_spinLinearCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) *
        ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
  rw [ons_loopWeight_KWmatWeightedPhase,
    ons_spinPhase_product_eq_homology a b d hvalid hsite hnu]

theorem ons_loopWeight_weightedPhase_eq_spinCharacter
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
    (hgeom : ∏ k, ons_turnW omega (d (k + 1)).2 (d k).2 =
      -(ons_spinCharacter 0 0
        (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ)) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) *
        ∏ k, weight (ons_portEdge L (d k)) := by
  rw [ons_loopWeight_weightedPhase_eq_homology
    weight omega a b d hvalid hsite hnu,
    ons_loopWeight_KWmatWeighted_eq weight omega d hvalid, hgeom]
  have hchar := ons_spinLinear_mul_quadratic a b
    (ons_evenHomology L (ons_dartEdgeSet d))
  calc
    ons_spinLinearCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) *
        ((∏ k, weight (ons_portEdge L (d k))) *
          -(ons_spinCharacter 0 0
            (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ)) =
      -(ons_spinLinearCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) *
        (ons_spinCharacter 0 0
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ)) *
          ∏ k, weight (ons_portEdge L (d k)) := by ring
    _ = -(ons_spinCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) *
          ∏ k, weight (ons_portEdge L (d k)) := by rw [hchar]

end StatMech.Onsager
