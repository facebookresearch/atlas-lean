/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Code.Universality.HexBoundaryIdentityClose
import Code.Universality.HexBridgeRealizeClose
import Code.Universality.HexZDivTauClose
import Code.Universality.HexHammersleyWelshClose

namespace StatMech.Universality

open Filter Topology
open scoped Topology Real NNReal BigOperators


















theorem hxf_bdry_combined {Iυ Ila : Type}
    (Eυ : HexColumnEmb ℕ Iυ) (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ)
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
    (hτEq : ∀ v, (B v).tau = tau v)
    (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v) :
    ∀ v, 1 ≤ v →
      hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1 := by
  intro v hv
  have h := hbi_hbdry_endgame B hFa v hv
  rw [hlamEq v, hτEq v, hυEq v] at h
  exact h
























theorem hxf_hexZ_chi_div (c : ℕ → ℝ)
    {Iυ Ila : Type} (Eυ : HexColumnEmb ℕ Iυ) (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ) (hτnn : ∀ v, 0 ≤ tau v)
    
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
    (hτEq : ∀ v, (B v).tau = tau v)
    (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
    (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
    (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
    
    (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
    
    {Iτ : Type} (S : HexSideContour Iτ tau)
    (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  set ups : ℕ → ℝ := Eυ.fiberSum with hupsdef
  set lam : ℕ → ℝ := hbr_lamCum (Ela.fiberSum) with hlamdef
  
  have hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1 := by
    intro v hv
    rw [hlamdef, hupsdef]
    exact hxf_bdry_combined Eυ Ela tau B hFa hlamEq hτEq hυEq v hv
  
  have hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1) := by
    intro v _
    exact hbr_cutB_of_bijection Eυ (Cut v) v (eB v) (hwB v)
  
  have hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v := by
    intro v _
    refine hbr_cutD_of_bijection Ela (Cut v) lam v ?_ (eD v) (hwD v)
    rw [hlamdef]; exact hbr_lamCum_telescope (Ela.fiberSum) v
  
  have hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1) := by
    intro v _
    rw [hlamdef]
    exact hbr_lamCum_mono (Ela.fiberSum) (fun n => hbr_fiberSum_nonneg Ela n) v
  
  have hυnn : ∀ v, 0 ≤ ups v := fun v => hbr_fiberSum_nonneg Eυ v
  
  have hEυc : Eυ.fiberSum = ups := rfl
  
  
  exact hexZ_chi_div_seams_closed c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB S.Eτ hEτ (hzd_tau_side_diverges S) Eυ hEυ hEυc








































theorem hxf_hex_connective_constant
    (c : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    
    {Iυ Ila : Type} (Eυ : HexColumnEmb ℕ Iυ) (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ) (hτnn : ∀ v, 0 ≤ tau v)
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
    (hτEq : ∀ v, (B v).tau = tau v)
    (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
    (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
    (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
    (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
    
    {Iτ : Type} (S : HexSideContour Iτ tau)
    (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    
    (Col : ∀ T, HexColumn T hexChiE)
    (HW : ∀ x, 0 < x → x < hexChiE →
      ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  
  have hdiv : ¬ Summable (fun n => c n * hexChiE ^ n) :=
    hxf_hexZ_chi_div c Eυ Ela tau hτnn B hFa hlamEq hτEq hυEq
      Cut eB hwB eD hwD hυpos S hEτ hEυ
  
  have hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n) :=
    hexConnAssembly_conv c (fun n => le_trans zero_le_one (hge n)) Col HW
  
  exact hex_connective_constant c hge hsub hdiv hconv




















theorem hxf_hexChiE_lt_one : hexChiE < 1 := by
  unfold hexChiE; rw [div_lt_one hex_sqrt_pos]
  calc (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt (2 + Real.sqrt 2) := by
        apply Real.sqrt_lt_sqrt (by norm_num); have := Real.sqrt_nonneg 2; linarith


theorem hxf_one_le_chiInv : 1 ≤ hexChiE⁻¹ := by
  rw [le_inv_comm₀ one_pos hexChiE_pos, inv_one]; exact le_of_lt hxf_hexChiE_lt_one


noncomputable def hxf_wc : ℕ → ℝ := fun n => (hexChiE⁻¹) ^ n


theorem hxf_wc_wt (n : ℕ) : hxf_wc n * hexChiE ^ n = 1 := by
  unfold hxf_wc; rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero n (ne_of_gt hexChiE_pos))]


theorem hxf_wc_wt_nn (n : ℕ) : 0 ≤ hxf_wc n * hexChiE ^ n := by rw [hxf_wc_wt]; norm_num



noncomputable def hxf_wEυ : HexColumnEmb ℕ ℕ where
  wtSAW := fun n => hxf_wc n * hexChiE ^ n
  emb := id
  emb_inj := Function.injective_id
  wtSAW_nn := hxf_wc_wt_nn
  scale := id


theorem hxf_wEυ_fiberSum (v : ℕ) : hxf_wEυ.fiberSum v = 1 := by
  unfold HexColumnEmb.fiberSum
  have huniq : ∀ a : {i : ℕ // hxf_wEυ.scale i = v}, a = ⟨v, rfl⟩ := fun a => Subtype.ext a.2
  rw [tsum_eq_single ⟨v, rfl⟩ (fun b hb => absurd (huniq b) hb)]
  show hxf_wc v * hexChiE ^ v = 1
  exact hxf_wc_wt v


noncomputable def hxf_wEla : HexColumnEmb ℕ Empty where
  wtSAW := fun n => hxf_wc n * hexChiE ^ n
  emb := Empty.elim
  emb_inj := fun a => a.elim
  wtSAW_nn := hxf_wc_wt_nn
  scale := Empty.elim


theorem hxf_wEla_lamCum (v : ℕ) : hbr_lamCum (hxf_wEla.fiberSum) v = 0 := by
  unfold hbr_lamCum; apply Finset.sum_eq_zero; intro w _
  show hxf_wEla.fiberSum w = 0
  unfold HexColumnEmb.fiberSum
  haveI : IsEmpty {i : Empty // hxf_wEla.scale i = w} := ⟨fun x => x.1.elim⟩
  exact tsum_empty



noncomputable def hxf_wCut : HexHighestCut hexChiE⁻¹ where
  D := Empty
  B := Unit
  wtγ := Empty.elim
  wtB := fun _ => 1
  wtB_nn := fun _ => zero_le_one
  wtγ_nn := fun d => d.elim
  split := fun d => d.elim
  split_inj := fun d => d.elim
  weight_bound := fun d => d.elim
  D_summable := summable_empty
  B_summable := summable_of_hasFiniteSupport (Set.toFinite _)


noncomputable def hxf_wEB (v : ℕ) : hxf_wCut.B ≃ {i : ℕ // hxf_wEυ.scale i = v + 1} where
  toFun := fun _ => ⟨v + 1, rfl⟩
  invFun := fun _ => ()
  left_inv := fun _ => rfl
  right_inv := fun i => Subtype.ext i.2.symm


noncomputable def hxf_wED (v : ℕ) : hxf_wCut.D ≃ {i : Empty // hxf_wEla.scale i = v + 1} where
  toFun := fun d => d.elim
  invFun := fun i => i.1.elim
  left_inv := fun d => d.elim
  right_inv := fun i => i.1.elim


noncomputable def hxf_wSideEτ : HexContourEmb ℕ ℕ where
  wtSAW := fun n => hxf_wc n * hexChiE ^ n
  emb := id
  emb_inj := Function.injective_id
  wtSAW_nn := hxf_wc_wt_nn




noncomputable def hxf_wSide : HexSideContour ℕ (fun _ => (0:ℝ)) where
  Eτ := hxf_wSideEτ
  posWit := fun ⟨_, _, hpos⟩ => absurd hpos (by norm_num)
  shift := fun i n => i + n
  shift_inj := fun i => add_right_injective i
  shift_wt := fun i n => by
    show hxf_wSideEτ.wtContour (i + n) = hxf_wSideEτ.wtContour i
    unfold HexContourEmb.wtContour
    show hxf_wc (i + n) * hexChiE ^ (i + n) = hxf_wc i * hexChiE ^ i
    rw [hxf_wc_wt, hxf_wc_wt]








theorem hxf_divergence_witness :
    ¬ Summable (fun n => hxf_wc n * hexChiE ^ n) :=
  hxf_hexZ_chi_div hxf_wc hxf_wEυ hxf_wEla (fun _ => 0) (fun _ => le_refl 0)
    (fun _ => hbi_witness) (fun _ _ => rfl)
    (fun v => (hxf_wEla_lamCum v).symm) (fun _ => rfl) (fun v => (hxf_wEυ_fiberSum v).symm)
    (fun _ => hxf_wCut) hxf_wEB
    (fun v _ => by show (1:ℝ) = hxf_wc (v + 1) * hexChiE ^ (v + 1); rw [hxf_wc_wt])
    hxf_wED (fun _ d => d.elim)
    (fun v _ => by rw [hxf_wEυ_fiberSum]; norm_num)
    hxf_wSide rfl rfl




theorem hxf_divergence_witness_consistent : ¬ Summable (fun _ : ℕ => (1:ℝ)) := by
  have h := hxf_divergence_witness
  have heq : (fun n => hxf_wc n * hexChiE ^ n) = (fun _ : ℕ => (1:ℝ)) := by
    funext n; exact hxf_wc_wt n
  rwa [heq] at h





theorem hxf_wc_saw_facts :
    (∀ n, 1 ≤ hxf_wc n) ∧ Submultiplicative hxf_wc := by
  refine ⟨fun n => ?_, fun m n => ?_⟩
  · exact one_le_pow₀ hxf_one_le_chiInv
  · show (hexChiE⁻¹) ^ (m + n) ≤ (hexChiE⁻¹) ^ m * (hexChiE⁻¹) ^ n
    rw [pow_add]

end StatMech.Universality
