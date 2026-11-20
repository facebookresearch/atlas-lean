/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexConnEndgame

namespace StatMech.Universality

open Filter Topology
open scoped Topology BigOperators













theorem hexBr_pow_decay (x χ : ℝ) (T n : ℕ) (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) (hn : T ≤ n) :
    x ^ n ≤ (x / χ) ^ T * χ ^ n := by
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hχ T)]
  rw [show n = T + (n - T) by omega, pow_add, pow_add]
  have key : x ^ (n - T) ≤ χ ^ (n - T) := pow_le_pow_left₀ hx hxχ _
  nlinarith [pow_nonneg hx T, pow_pos hχ T, pow_nonneg hx (n - T), pow_pos hχ (n - T),
    mul_le_mul_of_nonneg_left key (mul_nonneg (pow_nonneg hx T) (le_of_lt (pow_pos hχ T)))]












structure HexColumn (T : ℕ) (χ : ℝ) where
  
  W : Type
  
  len : W → ℕ
  
  len_ge : ∀ w, T ≤ len w
  
  crit_summable : Summable (fun w => χ ^ len w)
  
  crit_le_one : (∑' w, χ ^ len w) ≤ 1

namespace HexColumn

variable {T : ℕ} {χ : ℝ}


noncomputable def colSum (C : HexColumn T χ) (y : ℝ) : ℝ := ∑' w, y ^ C.len w



theorem colSum_crit_summable (C : HexColumn T χ) : Summable (fun w => χ ^ C.len w) :=
  C.crit_summable



theorem colSum_summable (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) : Summable (fun w => x ^ C.len w) :=
  (C.crit_summable.mul_left ((x / χ) ^ T)).of_nonneg_of_le
    (fun w => by positivity)
    (fun w => hexBr_pow_decay x χ T (C.len w) hx hχ hxχ (C.len_ge w))




theorem colSum_le_decay (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) :
    C.colSum x ≤ (x / χ) ^ T * C.colSum χ := by
  have hsx := C.colSum_summable hx hχ hxχ
  unfold colSum
  calc (∑' w, x ^ C.len w)
      ≤ ∑' w, (x / χ) ^ T * χ ^ C.len w :=
        hsx.tsum_mono (C.crit_summable.mul_left _)
          (fun w => hexBr_pow_decay x χ T (C.len w) hx hχ hxχ (C.len_ge w))
    _ = (x / χ) ^ T * ∑' w, χ ^ C.len w := tsum_mul_left




theorem colSum_le_pow (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) :
    C.colSum x ≤ (x / χ) ^ T := by
  have hpow_nn : (0 : ℝ) ≤ (x / χ) ^ T := by positivity
  calc C.colSum x ≤ (x / χ) ^ T * C.colSum χ := C.colSum_le_decay hx hχ hxχ
    _ ≤ (x / χ) ^ T * 1 := by
        apply mul_le_mul_of_nonneg_left C.crit_le_one hpow_nn
    _ = (x / χ) ^ T := mul_one _


theorem colSum_nonneg (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ C.colSum x := by
  unfold colSum
  exact tsum_nonneg (fun w => by positivity)

end HexColumn













structure HexContourEmb (W I : Type*) where
  
  wtSAW : W → ℝ
  
  emb : I → W
  
  emb_inj : Function.Injective emb
  
  wtSAW_nn : ∀ w, 0 ≤ wtSAW w

namespace HexContourEmb

variable {W I : Type*} (E : HexContourEmb W I)



def wtContour (i : I) : ℝ := E.wtSAW (E.emb i)





theorem summable_of_summable (hZ : Summable E.wtSAW) : Summable E.wtContour :=
  hZ.comp_injective E.emb_inj





theorem not_summable_of_not_summable (hI : ¬ Summable E.wtContour) :
    ¬ Summable E.wtSAW :=
  fun hZ => hI (E.summable_of_summable hZ)





theorem tsum_le (hZ : Summable E.wtSAW) :
    (∑' i, E.wtContour i) ≤ ∑' w, E.wtSAW w :=
  Summable.tsum_le_tsum_of_inj E.emb E.emb_inj (fun c _ => E.wtSAW_nn c)
    (fun _ => le_refl _) (E.summable_of_summable hZ) hZ

end HexContourEmb







structure HexColumnEmb (W I : Type*) where
  
  wtSAW : W → ℝ
  
  emb : I → W
  
  emb_inj : Function.Injective emb
  
  wtSAW_nn : ∀ w, 0 ≤ wtSAW w
  
  scale : I → ℕ

namespace HexColumnEmb

variable {W I : Type*} (E : HexColumnEmb W I)


noncomputable def fiberSum (v : ℕ) : ℝ :=
  ∑' i : {i // E.scale i = v}, E.wtSAW (E.emb i.1)





theorem fiberSum_summable (hZ : Summable E.wtSAW) :
    Summable E.fiberSum := by
  
  have htot : Summable (fun i => E.wtSAW (E.emb i)) := hZ.comp_injective E.emb_inj
  have hnn : ∀ i, 0 ≤ E.wtSAW (E.emb i) := fun i => E.wtSAW_nn _
  
  have hsig : Summable
      (fun p : Σ v : ℕ, {i // E.scale i = v} => E.wtSAW (E.emb p.2.1)) := by
    have h := ((Equiv.sigmaFiberEquiv E.scale).summable_iff
      (f := fun i => E.wtSAW (E.emb i))).mpr htot
    refine h.congr (fun p => ?_)
    rw [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
  exact (summable_sigma_of_nonneg (fun p => hnn _) |>.mp hsig).2

end HexColumnEmb























structure HexHighestCut (K : ℝ) where
  
  D : Type
  
  B : Type
  
  wtγ : D → ℝ
  
  wtB : B → ℝ
  
  wtB_nn : ∀ b, 0 ≤ wtB b
  
  wtγ_nn : ∀ d, 0 ≤ wtγ d
  
  split : D → B × B
  
  split_inj : Function.Injective split
  
  weight_bound : ∀ d, wtγ d ≤ K * (wtB (split d).1 * wtB (split d).2)
  
  D_summable : Summable wtγ
  
  B_summable : Summable wtB

namespace HexHighestCut

variable {K : ℝ}









theorem recursion_bound (H : HexHighestCut K) (hK : 0 ≤ K) :
    (∑' d, H.wtγ d) ≤ K * (∑' b, H.wtB b) ^ 2 := by
  
  have hprodSumm : Summable (fun p : H.B × H.B => H.wtB p.1 * H.wtB p.2) :=
    H.B_summable.mul_of_nonneg H.B_summable H.wtB_nn H.wtB_nn
  have hprodEq : (∑' p : H.B × H.B, H.wtB p.1 * H.wtB p.2) = (∑' b, H.wtB b) ^ 2 := by
    rw [sq, ← H.B_summable.tsum_mul_tsum H.B_summable hprodSumm]
  
  have hcompSumm : Summable (fun d => H.wtB (H.split d).1 * H.wtB (H.split d).2) :=
    hprodSumm.comp_injective H.split_inj
  have hcompLe :
      (∑' d, H.wtB (H.split d).1 * H.wtB (H.split d).2)
        ≤ ∑' p : H.B × H.B, H.wtB p.1 * H.wtB p.2 := by
    have := Summable.tsum_le_tsum_of_inj H.split H.split_inj
      (fun c _ => mul_nonneg (H.wtB_nn c.1) (H.wtB_nn c.2)) (fun _ => le_refl _)
      hcompSumm hprodSumm
    simpa using this
  calc (∑' d, H.wtγ d)
      ≤ ∑' d, K * (H.wtB (H.split d).1 * H.wtB (H.split d).2) :=
        H.D_summable.tsum_mono (hcompSumm.mul_left K) H.weight_bound
    _ = K * ∑' d, H.wtB (H.split d).1 * H.wtB (H.split d).2 := tsum_mul_left
    _ ≤ K * (∑' p : H.B × H.B, H.wtB p.1 * H.wtB p.2) :=
        mul_le_mul_of_nonneg_left hcompLe hK
    _ = K * (∑' b, H.wtB b) ^ 2 := by rw [hprodEq]

end HexHighestCut





























structure HexHWData (c : ℕ → ℝ) (υ : ℕ → ℝ) (x : ℝ) (N : ℕ) where
  
  S : Type
  
  Dn : Type
  
  Dn_fintype : Fintype Dn
  
  wtγ : Dn → ℝ
  
  wtS : S → ℝ
  
  wtγ_nn : ∀ d, 0 ≤ wtγ d
  
  wtS_nn : ∀ s, 0 ≤ wtS s
  
  S_summable : Summable wtS
  
  partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n
  
  half_sum_eq : (∑' s, wtS s) = ∏' T, (1 + υ T)
  
  decomp : Dn → S × S
  
  decomp_inj : Function.Injective decomp
  
  weight_bound : ∀ d, wtγ d ≤ wtS (decomp d).1 * wtS (decomp d).2

attribute [instance] HexHWData.Dn_fintype

namespace HexHWData

variable {c υ : ℕ → ℝ} {x : ℝ} {N : ℕ}









theorem partial_bound (H : HexHWData c υ x N) :
    ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (∏' T, (1 + υ T)) ^ 2 := by
  classical
  
  have hprodSumm : Summable (fun p : H.S × H.S => H.wtS p.1 * H.wtS p.2) :=
    H.S_summable.mul_of_nonneg H.S_summable H.wtS_nn H.wtS_nn
  have hprodEq : (∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2) = (∑' s, H.wtS s) ^ 2 := by
    rw [sq, ← H.S_summable.tsum_mul_tsum H.S_summable hprodSumm]
  
  have hcap : (∑ d, H.wtγ d) ≤ (∑' s, H.wtS s) ^ 2 := by
    calc (∑ d, H.wtγ d)
        ≤ ∑ d : H.Dn, H.wtS (H.decomp d).1 * H.wtS (H.decomp d).2 :=
          Finset.sum_le_sum (fun d _ => H.weight_bound d)
      _ = ∑ p ∈ Finset.univ.image H.decomp, H.wtS p.1 * H.wtS p.2 := by
          rw [Finset.sum_image (fun a _ b _ h => H.decomp_inj h)]
      _ ≤ ∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2 :=
          Summable.sum_le_tsum _ (fun p _ => mul_nonneg (H.wtS_nn _) (H.wtS_nn _)) hprodSumm
      _ = (∑' s, H.wtS s) ^ 2 := hprodEq
  
  rw [← H.partial_eq]
  calc (∑ d, H.wtγ d) ≤ (∑' s, H.wtS s) ^ 2 := hcap
    _ = (∏' T, (1 + υ T)) ^ 2 := by rw [H.half_sum_eq]
    _ ≤ 2 * (∏' T, (1 + υ T)) ^ 2 := by nlinarith [sq_nonneg (∏' T, (1 + υ T))]

end HexHWData





















theorem hexZ_conv_from_geometry (c : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hlt : x < hexChiE)
    (hc : ∀ n, 0 ≤ c n)
    (C : ∀ T, HexColumn T hexChiE)
    (H : ∀ N, HexHWData c (fun T => (C T).colSum x) x N) :
    Summable (fun n => c n * x ^ n) := by
  set upsx : ℕ → ℝ := fun T => (C T).colSum x with hupsx
  refine hexZ_conv c upsx x hx hlt hc ?_ ?_ ?_
  · 
    intro T; exact (C T).colSum_nonneg hx
  · 
    intro T; exact (C T).colSum_le_pow hx hexChiE_pos (le_of_lt hlt)
  · 
    intro N; exact (H N).partial_bound






theorem hexRec_term_of_cut (lam ups : ℕ → ℝ) (v : ℕ)
    (Cut : HexHighestCut hexChiE)
    (hD : (∑' d, Cut.wtγ d) = lam (v + 1) - lam v)
    (hB : (∑' b, Cut.wtB b) = ups (v + 1)) :
    lam (v + 1) - lam v ≤ hexChiE * (ups (v + 1)) ^ 2 := by
  have hrb := Cut.recursion_bound (le_of_lt hexChiE_pos)
  rw [hD, hB] at hrb
  exact hrb




















theorem hexZ_chi_div_from_geometry (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  have hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE * (ups (v + 1)) ^ 2 :=
    fun v hv => hexRec_term_of_cut lam ups v (Cut v) (hCutD v hv) (hCutB v hv)
  
  have hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n) := by
    intro hex
    have := Eτ.not_summable_of_not_summable (hτdiv hex)
    rw [hEτ] at this
    exact this
  
  have hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups := by
    intro hZ
    rw [← hEυ] at hZ
    have := Eυ.fiberSum_summable hZ
    rw [hEυc] at this
    exact this
  exact hexZ_chi_div c lam tau ups hbdry hrec hlamMono hυpos hυnn hτnn hτcol hυemb

end StatMech.Universality
