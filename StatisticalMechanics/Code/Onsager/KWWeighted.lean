/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWPhaseLoops
import Code.Onsager.TorusDecoration










namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_KWmatWeighted (L : ℕ)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 =>
    if d2.1 = ons_dirStep L d1.2 d1.1 then
      weight (ons_portEdge L d1) * ons_turnW omega d1.2 d2.2
    else 0

theorem ons_KWmatWeighted_const (L : ℕ) (x omega : ℂ) :
    ons_KWmatWeighted L (fun _ => x) omega = ons_KWmat L x omega := by
  ext d2 d1
  simp only [ons_KWmatWeighted, ons_KWmat]

theorem ons_loopWeight_KWmatWeighted_eq
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega : ℂ)
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_loopWeight (ons_KWmatWeighted L weight omega) d =
      (∏ k, weight (ons_portEdge L (d k))) *
        ∏ k, ons_turnW omega (d (k + 1)).2 (d k).2 := by
  unfold ons_loopWeight ons_KWmatWeighted
  have hfac : ∀ k : Fin n,
      (if (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 then
          weight (ons_portEdge L (d (k + 1))) *
            ons_turnW omega (d (k + 1)).2 (d k).2
        else 0) =
      weight (ons_portEdge L (d (k + 1))) *
        ons_turnW omega (d (k + 1)).2 (d k).2 := by
    intro k
    rw [if_pos (hvalid k)]
  rw [Finset.prod_congr rfl (fun k _ => hfac k),
    Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => weight (ons_portEdge L (d k)))

noncomputable def ons_KWmatWeightedPhase (L : ℕ)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 =>
    ons_dirPhase u v d1.2 * ons_KWmatWeighted L weight omega d2 d1

theorem ons_KWmatWeightedPhase_const (L : ℕ) (x omega u v : ℂ) :
    ons_KWmatWeightedPhase L (fun _ => x) omega u v =
      ons_KWmatPhase L x omega u v := by
  ext d2 d1
  simp only [ons_KWmatWeightedPhase, ons_KWmatWeighted_const,
    ons_KWmatPhase]

theorem ons_loopWeight_KWmatWeightedPhase
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega u v) d =
      (∏ k, ons_dirPhase u v (d k).2) *
        ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
  unfold ons_loopWeight ons_KWmatWeightedPhase
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => ons_dirPhase u v (d k).2)

end StatMech.Onsager
