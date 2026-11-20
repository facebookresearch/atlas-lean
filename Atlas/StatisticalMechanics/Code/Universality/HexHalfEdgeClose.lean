/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































































import Code.Universality.HexW2Weight
import Code.Universality.HexPerScaleBijClose

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators














noncomputable def hhe_rho (h h' : ℤ) : ℂ := hexUnit h' * (hexUnit h)⁻¹


theorem hhe_rho_norm (h h' : ℤ) : ‖hhe_rho h h'‖ = 1 := by
  unfold hhe_rho
  rw [norm_mul, norm_inv, norm_hexUnit, norm_hexUnit]; norm_num


theorem hhe_rho_ne_zero (h h' : ℤ) : hhe_rho h h' ≠ 0 := by
  intro hz; have := hhe_rho_norm h h'; rw [hz] at this; simp at this



theorem hhe_hexUnit_add (k s : ℤ) :
    hexUnit (k + s) = hexUnit k * Complex.exp (Complex.I * ((s : ℝ) * (Real.pi / 3))) := by
  unfold hexUnit
  rw [← Complex.exp_add]; congr 1; push_cast; ring





theorem hhe_halfStep_shift (h h' : ℤ) (s : ℤ) :
    halfStep (h' + s) = hhe_rho h h' * halfStep (h + s) := by
  unfold halfStep hhe_rho
  rw [hhe_hexUnit_add h' s, hhe_hexUnit_add h s]
  have hh : hexUnit h ≠ 0 := hexUnit_ne_zero h
  field_simp









theorem hhe_verticesAux_rigid (h h' : ℤ) (ts : List ℤ) :
    ∀ (m m' : ℂ) (s : ℤ),
      verticesAux m' (h' + s) ts
        = (verticesAux m (h + s) ts).map (fun z => hhe_rho h h' * (z - m) + m') := by
  induction ts with
  | nil =>
    intro m m' s
    simp only [verticesAux_nil, List.map_cons, List.map_nil]
    congr 1
    rw [hhe_halfStep_shift h h' s]; ring
  | cons t ts ih =>
    intro m m' s
    rw [verticesAux_cons, verticesAux_cons, List.map_cons]
    congr 1
    · rw [hhe_halfStep_shift h h' s]; ring
    · have key := ih (m + halfStep (h + s) + halfStep (h + s + t))
        (m' + halfStep (h' + s) + halfStep (h' + s + t)) (s + t)
      rw [show h' + (s + t) = h' + s + t by ring, show h + (s + t) = h + s + t by ring] at key
      rw [key]
      apply List.map_congr_left
      intro z _
      rw [hhe_halfStep_shift h h' s,
          show h' + s + t = h' + (s + t) by ring, hhe_halfStep_shift h h' (s + t),
          show h + (s + t) = h + s + t by ring]
      ring



theorem hhe_verticesAux_rigid0 (h h' : ℤ) (ts : List ℤ) (m m' : ℂ) :
    verticesAux m' h' ts
      = (verticesAux m h ts).map (fun z => hhe_rho h h' * (z - m) + m') := by
  have := hhe_verticesAux_rigid h h' ts m m' 0
  simpa using this




theorem hhe_nodup_iff (h h' : ℤ) (ts : List ℤ) (m m' : ℂ) :
    (verticesAux m' h' ts).Nodup ↔ (verticesAux m h ts).Nodup := by
  rw [hhe_verticesAux_rigid0 h h' ts m m']
  have hrne := hhe_rho_ne_zero h h'
  have hinj : Function.Injective (fun z : ℂ => hhe_rho h h' * (z - m) + m') := by
    intro a b hab
    simp only at hab
    have h2 : hhe_rho h h' * (a - m) = hhe_rho h h' * (b - m) := by linear_combination hab
    have := mul_left_cancel₀ hrne h2
    linear_combination this
  exact List.nodup_map_iff hinj



theorem hhe_isSAW_rebase (m m' : ℂ) (h h' : ℤ) (ts : List ℤ) :
    (ofTurns m' h' ts).IsSAW ↔ (ofTurns m h ts).IsSAW := by
  unfold IsSAW vertices ofTurns
  simp only
  exact hhe_nodup_iff h h' ts m m'



theorem hhe_legalTurns_rebase (m m' : ℂ) (h h' : ℤ) (ts : List ℤ) :
    (ofTurns m' h' ts).LegalTurns ↔ (ofTurns m h ts).LegalTurns := by
  unfold LegalTurns
  simp only [ofTurns_turns]




theorem hhe_isLegalSAW_rebase (m m' : ℂ) (h h' : ℤ) (ts : List ℤ) :
    (ofTurns m' h' ts).IsLegalSAW ↔ (ofTurns m h ts).IsLegalSAW := by
  unfold IsLegalSAW
  rw [hhe_legalTurns_rebase m m' h h' ts, hhe_isSAW_rebase m m' h h' ts]











theorem hhe_hexSAWwt_rebase (m m' : ℂ) (h h' : ℤ) (x : ℝ) (ts : List ℤ) :
    hexSAWwt m' h' x ts = hexSAWwt m h x ts := by
  unfold hexSAWwt
  by_cases hl : (HexWalk.ofTurns m h ts).IsLegalSAW
  · rw [if_pos hl, if_pos ((hhe_isLegalSAW_rebase m m' h h' ts).mpr hl)]
    simp only [numVertices, ofTurns]
  · rw [if_neg hl, if_neg (fun hc => hl ((hhe_isLegalSAW_rebase m m' h h' ts).mp hc))]



















structure HexHalvesInColumn (h0 : ℤ) (memD memB : List ℤ → Prop) where
  
  htake : ∀ d : {ts // memD ts}, memB (d.1.take (hexW2_cutPos h0 d.1))
  
  hdrop : ∀ d : {ts // memD ts}, memB (d.1.drop (hexW2_cutPos h0 d.1))















noncomputable def hhe_halfClass (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop)
    (htake : ∀ d : {ts // memD ts}, memB (d.1.take (hexW2_cutPos h0 d.1)))
    (hdrop : ∀ d : {ts // memD ts}, memB (d.1.drop (hexW2_cutPos h0 d.1))) :
    HexHalfClass a h0 x memD memB where
  lower := fun d => ⟨d.1.take (hexW2_cutPos h0 d.1), htake d⟩
  upper := fun d => ⟨d.1.drop (hexW2_cutPos h0 d.1), hdrop d⟩
  hlow := fun d => rfl
  hupp := fun d => by
    change hexSAWwt a h0 x (d.1.drop (hexW2_cutPos h0 d.1))
      = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
          (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1))
    exact (hhe_hexSAWwt_rebase a (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
      h0 (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1))).symm
  pair_inj := by
    intro d d' heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have htk : d.1.take (hexW2_cutPos h0 d.1) = d'.1.take (hexW2_cutPos h0 d'.1) :=
      congrArg Subtype.val h1
    have hdp : d.1.drop (hexW2_cutPos h0 d.1) = d'.1.drop (hexW2_cutPos h0 d'.1) :=
      congrArg Subtype.val h2
    apply Subtype.ext
    calc d.1 = d.1.take (hexW2_cutPos h0 d.1) ++ d.1.drop (hexW2_cutPos h0 d.1) :=
          (List.take_append_drop _ _).symm
      _ = d'.1.take (hexW2_cutPos h0 d'.1) ++ d'.1.drop (hexW2_cutPos h0 d'.1) := by
          rw [htk, hdp]
      _ = d'.1 := List.take_append_drop _ _



noncomputable def hhe_halfClass_of_halves (a : ℂ) (h0 : ℤ) (x : ℝ)
    (memD memB : List ℤ → Prop) (HIC : HexHalvesInColumn h0 memD memB) :
    HexHalfClass a h0 x memD memB :=
  hhe_halfClass a h0 x memD memB HIC.htake HIC.hdrop


@[simp] theorem hhe_halfClass_lower (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop)
    (htake hdrop) (d : {ts // memD ts}) :
    ((hhe_halfClass a h0 x memD memB htake hdrop).lower d).1
      = d.1.take (hexW2_cutPos h0 d.1) := rfl


@[simp] theorem hhe_halfClass_upper (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop)
    (htake hdrop) (d : {ts // memD ts}) :
    ((hhe_halfClass a h0 x memD memB htake hdrop).upper d).1
      = d.1.drop (hexW2_cutPos h0 d.1) := rfl

























theorem hhe_hexZ_chi_div (c : ℕ → ℝ) (a0 : ℂ) (h0 : ℤ)
    (memA memB : ℕ → List ℤ → Prop) (tau : ℕ → ℝ)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (HIC : ∀ v, HexHalvesInColumn h0
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)))
    (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
      hexSAWwt a0 h0 hexChiE d.1))
    (hBsum : ∀ v, Summable (fun b : {ts // memB (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1))
    (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a0 h0 hexChiE n.1))
    (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a0 h0 hexChiE (memA v)
        + hexCt * tau v + hpb_upsS a0 h0 hexChiE (memB v) = 1)
    (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a0 h0 hexChiE (memA v)
        ≤ hpb_lamS a0 h0 hexChiE (memA (v + 1)))
    (hυpos : ∀ v, 1 ≤ v → 0 < hpb_upsS a0 h0 hexChiE (memB v))
    (hτnn : ∀ v, 0 ≤ tau v)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = fun v => hpb_upsS a0 h0 hexChiE (memB v)) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hpb_hexZ_chi_div c a0 h0 memA memB tau hsub
    (fun v => hhe_halfClass_of_halves a0 h0 hexChiE
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)) (HIC v))
    hDsum hBsum hAsum hbdry hlamMono hυpos hτnn Eτ hEτ hτdiv Eυ hEυ hEυc












theorem hhe_singleRight_cutPos : hexW2_cutPos 0 [(-1 : ℤ)] = 1 := by
  have h1 := hexW2_singleRight_cutPos_pos
  have h2 := hexW2_cutPos_le 0 [(-1 : ℤ)]
  simp only [List.length_cons, List.length_nil] at h2
  omega



def hhe_singleRight_memB : List ℤ → Prop := fun ts => ts = [(-1 : ℤ)] ∨ ts = []







def hhe_singleRight_halvesInColumn :
    HexHalvesInColumn 0 hexW2_singleRight_memD hhe_singleRight_memB where
  htake := by
    intro d
    have hd : d.1 = [(-1 : ℤ)] := d.2
    rw [hd, hhe_singleRight_cutPos]
    left; rfl
  hdrop := by
    intro d
    have hd : d.1 = [(-1 : ℤ)] := d.2
    rw [hd, hhe_singleRight_cutPos]
    right; rfl








theorem hhe_singleRight_upper_fires (a : ℂ) (x : ℝ) :
    hexSAWwt a 0 x
        ((hhe_halfClass_of_halves a 0 x hexW2_singleRight_memD hhe_singleRight_memB
            hhe_singleRight_halvesInColumn).upper hexW2_singleRight_elt).1
      = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]))
          (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) x
          ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)])) :=
  (hhe_halfClass_of_halves a 0 x hexW2_singleRight_memD hhe_singleRight_memB
    hhe_singleRight_halvesInColumn).hupp hexW2_singleRight_elt

end StatMech.Universality
