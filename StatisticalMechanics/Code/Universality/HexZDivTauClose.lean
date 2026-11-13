/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































































import Mathlib
import Code.Universality.HexBridge
import Code.Universality.HexBridgeRecon
import Code.Universality.HexConnEndgame
import Code.Universality.HexW2Summable

namespace StatMech.Universality

open Filter Topology Complex HexWalk
open scoped Topology BigOperators













theorem hzd_not_summable_const {c : ℝ} (hc : c ≠ 0) :
    ¬ Summable (fun _ : ℕ => c) := by
  intro hsum
  have h0 := hsum.tendsto_atTop_zero
  have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  exact hc (tendsto_nhds_unique hconst h0)








theorem hzd_not_summable_of_const_inj {I : Type*} (w : I → ℝ) (c : ℝ) (hc : 0 < c)
    (g : ℕ → I) (hg : Function.Injective g) (hconst : ∀ n, w (g n) = c) :
    ¬ Summable w := by
  intro hsum
  have hcomp : Summable (fun n : ℕ => w (g n)) := hsum.comp_injective hg
  have heq : (fun n : ℕ => w (g n)) = fun _ : ℕ => c := by
    funext n; exact hconst n
  rw [heq] at hcomp
  exact hzd_not_summable_const (ne_of_gt hc) hcomp













theorem hzd_vertShift_injective (mid period : ℂ) (hp : period ≠ 0) :
    Function.Injective (fun h : ℕ => mid + period * (h : ℂ)) := by
  intro a b hab
  simp only [add_right_inj] at hab
  exact_mod_cast mul_left_cancel₀ hp hab






theorem hzd_sawwt_vertShift (mid period : ℂ) (head : ℤ) (x : ℝ) (turns : List ℤ)
    (h : ℕ) :
    hexSAWwt (mid + period * (h : ℂ)) head x turns = hexSAWwt mid head x turns :=
  hexW2S_hexSAWwt_mid_indep mid (mid + period * (h : ℂ)) head x turns

































structure HexSideContour (Iτ : Type) (tau : ℕ → ℝ) where
  
  Eτ : HexContourEmb ℕ Iτ
  
  posWit : (∃ v, 1 ≤ v ∧ 0 < tau v) → ∃ i₀ : Iτ, 0 < Eτ.wtContour i₀
  
  shift : Iτ → ℕ → Iτ
  
  shift_inj : ∀ i, Function.Injective (shift i)
  
  shift_wt : ∀ i n, Eτ.wtContour (shift i n) = Eτ.wtContour i









theorem hzd_tau_side_diverges {Iτ : Type} {tau : ℕ → ℝ} (S : HexSideContour Iτ tau) :
    (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable S.Eτ.wtContour := by
  intro hex
  obtain ⟨i₀, hpos⟩ := S.posWit hex
  exact hzd_not_summable_of_const_inj S.Eτ.wtContour (S.Eτ.wtContour i₀) hpos
    (S.shift i₀) (S.shift_inj i₀) (fun n => S.shift_wt i₀ n)





















theorem hzd_hexZ_chi_div_tauClosed (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (S : HexSideContour Iτ tau)
    (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hexZ_chi_div_from_geometry_recon c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB S.Eτ hEτ (hzd_tau_side_diverges S) Eυ hEυ hEυc















theorem hzd_trivial_wt : hexSAWwt (0 : ℂ) 0 hexChiE [] = hexChiE := by
  rw [hexSAWwt_of_isLegalSAW 0 0 hexChiE (HexWalk.trivialWalk_isLegalSAW 0 0)]
  rw [show (HexWalk.ofTurns (0 : ℂ) 0 []).numVertices = 1 from rfl, pow_one]






noncomputable def hzd_witnessEτ : HexContourEmb ℕ ℕ where
  wtSAW := fun _ => hexSAWwt (0 : ℂ) 0 hexChiE []
  emb := id
  emb_inj := Function.injective_id
  wtSAW_nn := fun _ => hexSAWwt_nonneg 0 0 (le_of_lt hexChiE_pos) []



theorem hzd_witnessEτ_wtContour (h : ℕ) :
    hzd_witnessEτ.wtContour h = hexChiE := hzd_trivial_wt





noncomputable def hzd_witnessSideContour : HexSideContour ℕ (fun _ => (1 : ℝ)) where
  Eτ := hzd_witnessEτ
  posWit := fun _ => ⟨0, by rw [hzd_witnessEτ_wtContour]; exact hexChiE_pos⟩
  shift := fun h n => h + n
  shift_inj := fun h => add_right_injective h
  shift_wt := fun h n => by
    rw [hzd_witnessEτ_wtContour, hzd_witnessEτ_wtContour]









theorem hzd_sideContour_fires :
    ¬ Summable hzd_witnessEτ.wtContour :=
  hzd_tau_side_diverges hzd_witnessSideContour ⟨1, le_rfl, one_pos⟩

end StatMech.Universality
