/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































































import Mathlib
import Code.Universality.HexW2Weight
import Code.Universality.HexBridgeRealizeClose
import Code.Universality.HexZDivTauClose

namespace StatMech.Universality

open Complex Filter Topology
open scoped Topology BigOperators




























noncomputable def hbs_highestCut (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut_chi_weightClosed a h0 hexChiE_pos memD hDsum hBsum


@[simp] theorem hbs_highestCut_B (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    (hbs_highestCut a h0 memD hDsum hBsum).B = HexW2Half := rfl



@[simp] theorem hbs_highestCut_wtB (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    (hbs_highestCut a h0 memD hDsum hBsum).wtB = hexW2_halfWt hexChiE := rfl



@[simp] theorem hbs_highestCut_D (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    (hbs_highestCut a h0 memD hDsum hBsum).D = {ts // memD ts} := rfl



@[simp] theorem hbs_highestCut_wtγ (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE))
    (d : {ts // memD ts}) :
    (hbs_highestCut a h0 memD hDsum hBsum).wtγ d = hexSAWwt a h0 hexChiE d.1 := rfl

















theorem hbs_splitFields_closed (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    (∀ d : {ts // memD ts},
        (hbs_highestCut a h0 memD hDsum hBsum).wtB
            ((hbs_highestCut a h0 memD hDsum hBsum).split d).1
          = hexSAWwt a h0 hexChiE (d.1.take (hexW2_cutPos h0 d.1)))
      ∧ (∀ d : {ts // memD ts},
        (hbs_highestCut a h0 memD hDsum hBsum).wtB
            ((hbs_highestCut a h0 memD hDsum hBsum).split d).2
          = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
              (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) hexChiE
              (d.1.drop (hexW2_cutPos h0 d.1)))
      ∧ Function.Injective (hbs_highestCut a h0 memD hDsum hBsum).split :=
  ⟨fun d => hexW2_split_fst_wt a h0 hexChiE memD d,
   fun d => hexW2_split_snd_wt a h0 hexChiE memD d,
   hexW2_split_injective a h0 memD⟩

































theorem hbs_hexZ_chi_div_split_closed (c : ℕ → ℝ)
    {Iτ : Type} {tau : ℕ → ℝ} (S : HexSideContour Iτ tau) (hτnn : ∀ v, 0 ≤ tau v)
    {Iυ Ila : Type} (Eυ : HexColumnEmb ℕ Iυ) (Ela : HexColumnEmb ℕ Ila)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
    (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
    (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1)
    (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
    (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hbr_hexZ_chi_div_of_bijections c S.Eτ Eυ Ela tau hτnn Cut eB hwB eD hwD hbdry hυpos
    hEτ (hzd_tau_side_diverges S) hEυ
















theorem hbs_split_fires (a : ℂ) :
    hexW2_halfWt hexChiE (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).1
        = hexSAWwt a 0 hexChiE ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)]))
      ∧ hexW2_halfWt hexChiE (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).2
        = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]))
            (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) hexChiE
            ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)]))
      ∧ Function.Injective (hexW2_split a 0 hexW2_singleRight_memD) :=
  ⟨hexW2_split_fst_wt a 0 hexChiE hexW2_singleRight_memD hexW2_singleRight_elt,
   hexW2_split_snd_wt a 0 hexChiE hexW2_singleRight_memD hexW2_singleRight_elt,
   hexW2_split_injective a 0 hexW2_singleRight_memD⟩

end StatMech.Universality
