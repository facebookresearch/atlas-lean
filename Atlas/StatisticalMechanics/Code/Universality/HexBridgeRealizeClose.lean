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

namespace StatMech.Universality

open Filter Topology Complex
open scoped Topology BigOperators










theorem hbr_fiberSum_nonneg {W I : Type} (E : HexColumnEmb W I) (v : ℕ) :
    0 ≤ E.fiberSum v := by
  unfold HexColumnEmb.fiberSum
  exact tsum_nonneg (fun i => E.wtSAW_nn _)




theorem hbr_fiberSum_pos {W I : Type} (E : HexColumnEmb W I) (v : ℕ)
    (i0 : I) (hsc : E.scale i0 = v) (hpos : 0 < E.wtSAW (E.emb i0))
    (hsum : Summable (fun i : {i // E.scale i = v} => E.wtSAW (E.emb i.1))) :
    0 < E.fiberSum v := by
  unfold HexColumnEmb.fiberSum
  exact lt_of_lt_of_le hpos (hsum.le_tsum ⟨i0, hsc⟩ (fun j _ => E.wtSAW_nn _))
















theorem hbr_cutB_of_bijection {W Iυ : Type} (Eυ : HexColumnEmb W Iυ) {K : ℝ}
    (Cut : HexHighestCut K) (v : ℕ)
    (e : Cut.B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hw : ∀ b, Cut.wtB b = Eυ.wtSAW (Eυ.emb (e b).1)) :
    (∑' b, Cut.wtB b) = Eυ.fiberSum (v + 1) := by
  unfold HexColumnEmb.fiberSum
  rw [← Equiv.tsum_eq e (fun i => Eυ.wtSAW (Eυ.emb i.1))]
  exact tsum_congr hw











noncomputable def hbr_lamCum (f : ℕ → ℝ) (v : ℕ) : ℝ := ∑ w ∈ Finset.range (v + 1), f w




theorem hbr_lamCum_telescope (f : ℕ → ℝ) (v : ℕ) :
    hbr_lamCum f (v + 1) - hbr_lamCum f v = f (v + 1) := by
  unfold hbr_lamCum
  rw [Finset.sum_range_succ]
  ring




theorem hbr_lamCum_mono (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (v : ℕ) :
    hbr_lamCum f v ≤ hbr_lamCum f (v + 1) := by
  unfold hbr_lamCum
  rw [Finset.sum_range_succ (f := f) (n := v + 1)]
  linarith [hf (v + 1)]

















theorem hbr_cutD_of_bijection {W Ila : Type} (Ela : HexColumnEmb W Ila) {K : ℝ}
    (Cut : HexHighestCut K) (lam : ℕ → ℝ) (v : ℕ)
    (htel : lam (v + 1) - lam v = Ela.fiberSum (v + 1))
    (e : Cut.D ≃ {i : Ila // Ela.scale i = v + 1})
    (hw : ∀ d, Cut.wtγ d = Ela.wtSAW (Ela.emb (e d).1)) :
    (∑' d, Cut.wtγ d) = lam (v + 1) - lam v := by
  rw [htel]
  unfold HexColumnEmb.fiberSum
  rw [← Equiv.tsum_eq e (fun i => Ela.wtSAW (Ela.emb i.1))]
  exact tsum_congr hw






































theorem hbr_hexZ_chi_div_of_bijections (c : ℕ → ℝ)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    {Ila : Type} (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ) (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    
    (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
    (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
    (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
    
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1)
    
    (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
    
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  set ups : ℕ → ℝ := Eυ.fiberSum with hupsdef
  set lam : ℕ → ℝ := hbr_lamCum (Ela.fiberSum) with hlamdef
  
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
  
  exact hexZ_chi_div_from_geometry_recon c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc











noncomputable def hbr_witnessEmb : HexColumnEmb Unit Unit where
  wtSAW := fun _ => (1 : ℝ)
  emb := fun _ => ()
  emb_inj := fun a b _ => Subsingleton.elim a b
  wtSAW_nn := fun _ => zero_le_one
  scale := fun _ => 1



theorem hbr_witnessEmb_fiberSum_one : hbr_witnessEmb.fiberSum 1 = 1 := by
  unfold HexColumnEmb.fiberSum hbr_witnessEmb
  rw [tsum_eq_single ⟨(), rfl⟩ ?_]
  · intro b hb
    exact absurd (Subsingleton.elim b ⟨(), rfl⟩) hb








theorem hbr_bijection_fires {K : ℝ} (Cut : HexHighestCut K)
    (e : Cut.B ≃ {i : Unit // hbr_witnessEmb.scale i = 0 + 1})
    (hw : ∀ b, Cut.wtB b = hbr_witnessEmb.wtSAW (hbr_witnessEmb.emb (e b).1)) :
    (∑' b, Cut.wtB b) = 1 := by
  rw [hbr_cutB_of_bijection hbr_witnessEmb Cut 0 e hw, zero_add]
  exact hbr_witnessEmb_fiberSum_one

end StatMech.Universality
