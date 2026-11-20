/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeighted
import Code.Onsager.KWPhaseLemma5









namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_weight_product_surgery
    {L n : ℕ} [NeZero n] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (e : ons_Dart L) (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    (∏ k, weight (ons_portEdge L
      (ons_surgery e (ons_dartRev L) d k))) =
      ∏ k, weight (ons_portEdge L (d k)) := by
  rw [ons_mem_loopSetBoth] at hd
  let rev := ons_dartRev L
  have hrevinv : Function.Involutive rev := ons_dartRev_involutive L
  let l := ons_l e rev d
  let m := ons_m e rev d
  have hlm : l ≤ m := ons_l_le_m hrevinv hd
  let s := ons_surgery e rev d
  have hs : s = ons_revSeg rev l m d := ons_surgery_eq_revSeg hd
  let U : Finset (Fin n) :=
    Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m)
  let edgeWeight : ons_Dart L → ℂ := fun q => weight (ons_portEdge L q)
  let P : ℂ := ∏ k ∈ U, edgeWeight (d k)
  have hmirror : (∏ k ∈ U, edgeWeight (d (ons_mir l m k))) = P := by
    rw [show P = ∏ k ∈ U, edgeWeight (d k) from rfl]
    refine Finset.prod_bij'
      (fun k _ => ons_mir l m k) (fun k _ => ons_mir l m k)
      ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      change ons_mir l m k ∈ U
      simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using
        ons_mir_mem hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      change ons_mir l m k ∈ U
      simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using
        ons_mir_mem hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ons_mir_mir hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ons_mir_mir hk'.1 hk'.2
    · intro k _
      rfl
  have hinside : (∏ k ∈ U, edgeWeight (s k)) = P := by
    calc
      (∏ k ∈ U, edgeWeight (s k)) =
          ∏ k ∈ U, edgeWeight (d (ons_mir l m k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
          Finset.mem_filter] at hk
        have hsk : s k = rev (d (ons_mir l m k)) := by
          rw [hs]
          exact ons_revSeg_inside rev d hk.2.1 hk.2.2
        rw [hsk]
        exact congrArg weight (ons_portEdge_rev L (d (ons_mir l m k)))
      _ = P := hmirror
  have houtside :
      (∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), edgeWeight (s k)) =
        ∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), edgeWeight (d k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    have hsk : s k = d k := by
      rw [hs]
      exact ons_revSeg_outside rev d hk.2
    rw [hsk]
  calc
    (∏ k, edgeWeight (s k)) =
        (∏ k ∈ U, edgeWeight (s k)) *
          ∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), edgeWeight (s k) := by
      rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]
    _ = P * ∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)),
          edgeWeight (d k) := by rw [hinside, houtside]
    _ = ∏ k, edgeWeight (d k) := by
      rw [show P = ∏ k ∈ U, edgeWeight (d k) from rfl,
        show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]

theorem ons_loopWeight_KWmatWeighted_factor_one
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega : ℂ)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatWeighted L weight omega) d =
      (∏ k, weight (ons_portEdge L (d k))) *
        ons_loopWeight (ons_KWmat L 1 omega) d := by
  have hentry : ∀ k : Fin n,
      ons_KWmatWeighted L weight omega (d k) (d (k + 1)) =
        weight (ons_portEdge L (d (k + 1))) *
          ons_KWmat L 1 omega (d k) (d (k + 1)) := by
    intro k
    simp only [ons_KWmatWeighted, ons_KWmat]
    split <;> ring
  unfold ons_loopWeight
  rw [Finset.prod_congr rfl (fun k _ => hentry k),
    Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => weight (ons_portEdge L (d k)))

theorem ons_KWmatWeighted_surgery_sign
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (e : ons_Dart L) (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    ons_loopWeight (ons_KWmatWeighted L weight omega)
        (ons_surgery e (ons_dartRev L) d) =
      -ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
  rw [ons_loopWeight_KWmatWeighted_factor_one,
    ons_loopWeight_KWmatWeighted_factor_one,
    ons_weight_product_surgery weight e d hd,
    ons_KW_surgery_sign 1 omega homega e d hd]
  ring

theorem ons_KWmatWeightedPhase_surgery_sign
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_surgery e (ons_dartRev L) d) =
      -ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d := by
  have hsign := ons_KWmatWeighted_surgery_sign weight omega homega e d hd
  by_cases hzero : ons_loopWeight (ons_KWmatWeighted L weight omega) d = 0
  · have hszero : ons_loopWeight (ons_KWmatWeighted L weight omega)
        (ons_surgery e (ons_dartRev L) d) = 0 := by
      rw [hsign, hzero, neg_zero]
    rw [ons_loopWeight_KWmatWeightedPhase,
      ons_loopWeight_KWmatWeightedPhase, hzero, hszero]
    ring
  · have hone : ons_loopWeight (ons_KWmat L 1 omega) d ≠ 0 := by
      intro hone
      apply hzero
      rw [ons_loopWeight_KWmatWeighted_factor_one, hone, mul_zero]
    have hvalid : ∀ k : Fin n,
        (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 := by
      intro k
      by_contra hk
      apply hone
      unfold ons_loopWeight
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp only [ons_KWmat]
      exact if_neg hk
    have hphase := ons_spinPhase_surgeryFactor a b e d hd hvalid
    rw [ons_loopWeight_KWmatWeightedPhase,
      ons_loopWeight_KWmatWeightedPhase, hphase, hsign]
    ring



theorem ons_KWmatWeightedPhase_lemma5
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e),
      ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d = 0 := by
  apply ons_lemma5 _ e (ons_dartRev L)
    (ons_dartRev_involutive L) (ons_dartRev_ne L e)
  intro d hd
  exact ons_KWmatWeightedPhase_surgery_sign weight omega homega a b e d hd

theorem ons_weight_product_loopRev
    {L n : ℕ} [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (d : Fin n → ons_Dart L) :
    (∏ k, weight (ons_portEdge L (ons_loopRev L d k))) =
      ∏ k, weight (ons_portEdge L (d k)) := by
  simp only [ons_loopRev]
  calc
    (∏ k, weight (ons_portEdge L (ons_dartRev L (d (-k))))) =
        ∏ k, weight (ons_portEdge L (d (-k))) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [ons_portEdge_rev]
    _ = ∏ k, weight (ons_portEdge L (d k)) :=
      Equiv.prod_comp (Equiv.neg (Fin n))
        (fun k => weight (ons_portEdge L (d k)))

theorem ons_loopWeight_KWmatWeightedPhase_factor_one
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      (∏ k, weight (ons_portEdge L (d k))) *
        ons_loopWeight (ons_KWmatPhase L 1 omega
          (ons_spinPhase L a) (ons_spinPhase L b)) d := by
  rw [ons_loopWeight_KWmatWeightedPhase,
    ons_loopWeight_KWmatWeighted_factor_one,
    ons_loopWeight_KWmatPhase]
  ring

theorem ons_loopWeight_KWmatWeightedPhase_loopRev
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) (ons_loopRev L d) =
      ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d := by
  rw [ons_loopWeight_KWmatWeightedPhase_factor_one,
    ons_loopWeight_KWmatWeightedPhase_factor_one,
    ons_weight_product_loopRev weight d,
    ons_loopWeight_spinPhase_loopRev 1 omega homega a b d]

end StatMech.Onsager
