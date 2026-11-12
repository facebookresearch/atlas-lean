/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexConnEndgame
import Code.Universality.HexBridge
import Code.Universality.HexBridgeDecomp
import Code.Universality.HexBridgeRecon
import Code.Universality.HexSurgerySeams

namespace StatMech.Universality

open List
open scoped BigOperators












theorem hbw_widthlist_nodup (bs : List HexBridge) (h : StrictDecreasingWidths bs) :
    (bs.map HexBridge.width).Nodup := by
  have hp : (bs.map HexBridge.width).Pairwise (· ≠ ·) := by
    rw [List.pairwise_map]
    exact h.imp (fun hab => ne_of_gt hab)
  exact hp





noncomputable def hbw_widthFinset (bs : List HexBridge) : Finset ℕ :=
  (bs.map HexBridge.width).toFinset






theorem hbw_prod_eq_finsetProd (bs : List HexBridge) (h : StrictDecreasingWidths bs)
    (υ : ℕ → ℝ) :
    (bs.map (fun b => υ b.width)).prod = ∏ T ∈ hbw_widthFinset bs, υ T := by
  have hnd := hbw_widthlist_nodup bs h
  unfold hbw_widthFinset
  rw [List.prod_toFinset υ hnd, List.map_map]
  rfl





















theorem hbw_bridgeProd_le (bs : List HexBridge) (h : StrictDecreasingWidths bs)
    (υ wt : ℕ → ℝ) (hdom : ∀ b ∈ bs, wt b.width ≤ υ b.width)
    (hwtnn : ∀ b ∈ bs, 0 ≤ wt b.width) :
    (bs.map (fun b => wt b.width)).prod ≤ ∏ T ∈ hbw_widthFinset bs, υ T := by
  rw [← hbw_prod_eq_finsetProd bs h υ]
  exact List.prod_map_le_prod_map₀ (fun b => wt b.width) (fun b => υ b.width)
    (fun b hb => hwtnn b hb) (fun b hb => hdom b hb)




























theorem hbw_weightBound_factor (x g : ℝ) (hx : 0 < x)
    (lower upper : List HexBridge)
    (hlo : StrictDecreasingWidths lower) (hup : StrictDecreasingWidths upper)
    (υ wt : ℕ → ℝ)
    (hdomLo : ∀ b ∈ lower, wt b.width ≤ υ b.width)
    (hdomUp : ∀ b ∈ upper, wt b.width ≤ υ b.width)
    (hwtnn : ∀ T, 0 ≤ wt T)
    (htwo : g * x ^ 2 = (lower.map (fun b => wt b.width)).prod
                          * (upper.map (fun b => wt b.width)).prod) :
    g ≤ (x ^ 2)⁻¹ *
      ((∏ T ∈ hbw_widthFinset lower, υ T) * (∏ T ∈ hbw_widthFinset upper, υ T)) := by
  have hloProd : (lower.map (fun b => wt b.width)).prod ≤ ∏ T ∈ hbw_widthFinset lower, υ T :=
    hbw_bridgeProd_le lower hlo υ wt hdomLo (fun b _ => hwtnn b.width)
  have hupProd : (upper.map (fun b => wt b.width)).prod ≤ ∏ T ∈ hbw_widthFinset upper, υ T :=
    hbw_bridgeProd_le upper hup υ wt hdomUp (fun b _ => hwtnn b.width)
  have hloNN : (0 : ℝ) ≤ (lower.map (fun b => wt b.width)).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hupNN : (0 : ℝ) ≤ (upper.map (fun b => wt b.width)).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  
  have hg : g = (x ^ 2)⁻¹ * ((lower.map (fun b => wt b.width)).prod
                          * (upper.map (fun b => wt b.width)).prod) := by
    field_simp at htwo ⊢
    linarith [htwo]
  rw [hg]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul hloProd hupProd hupNN (le_trans hloNN hloProd)






























noncomputable def hexHWDataReconOfDomination (c : ℕ → ℝ) (υ : ℕ → ℝ) (x : ℝ) (N : ℕ)
    (hx : 0 < x)
    (hυnn : ∀ T, 0 ≤ υ T)
    (hmul : Multipliable (fun T => 1 + υ T))
    (Dn : Type) [Fintype Dn]
    (wtγ : Dn → ℝ) (wtγ_nn : ∀ d, 0 ≤ wtγ d)
    (partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n)
    (wt : ℕ → ℝ) (hwtnn : ∀ T, 0 ≤ wt T)
    (lower upper : Dn → List HexBridge)
    (hlo : ∀ d, StrictDecreasingWidths (lower d))
    (hup : ∀ d, StrictDecreasingWidths (upper d))
    (htwoEdge : ∀ d, wtγ d * x ^ 2
        = ((lower d).map (fun b => wt b.width)).prod
          * ((upper d).map (fun b => wt b.width)).prod)
    (hdomLo : ∀ d, ∀ b ∈ lower d, wt b.width ≤ υ b.width)
    (hdomUp : ∀ d, ∀ b ∈ upper d, wt b.width ≤ υ b.width)
    (decomp_inj : Function.Injective
      (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))) :
    HexHWDataRecon c υ x N :=
  hexHWDataClosed c υ x N hυnn hmul Dn wtγ wtγ_nn partial_eq
    (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))
    decomp_inj
    (fun d => hbw_weightBound_factor x (wtγ d) hx (lower d) (upper d) (hlo d) (hup d)
      υ wt (hdomLo d) (hdomUp d) hwtnn (htwoEdge d))








theorem hexZ_conv_domination (c : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hlt : x < hexChiE) (hc : ∀ n, 0 ≤ c n)
    (C : ∀ T, HexColumn T hexChiE)
    (H : ∀ N, HexHWDataRecon c (fun T => (C T).colSum x) x N) :
    Summable (fun n => c n * x ^ n) :=
  hexZ_conv_seams_closed c x hx hlt hc C H

end StatMech.Universality
