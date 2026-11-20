/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Mathlib
import Code.Universality.HexW2Cut
import Code.Universality.HexInfraWinding

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators















structure HexW2Half where
  
  mid : ℂ
  
  head : ℤ
  
  turns : List ℤ




noncomputable def hexW2_halfWt (x : ℝ) (b : HexW2Half) : ℝ :=
  hexSAWwt b.mid b.head x b.turns


theorem hexW2_halfWt_nonneg (x : ℝ) (hx : 0 ≤ x) (b : HexW2Half) :
    0 ≤ hexW2_halfWt x b :=
  hexSAWwt_nonneg b.mid b.head hx b.turns
















noncomputable def hexW2_lowerHalf (a : ℂ) (h0 : ℤ) (ts : List ℤ) : HexW2Half where
  mid := a
  head := h0
  turns := ts.take (hexW2_cutPos h0 ts)




noncomputable def hexW2_upperHalf (a : ℂ) (h0 : ℤ) (ts : List ℤ) : HexW2Half where
  mid := hexDropMid a h0 ts (hexW2_cutPos h0 ts)
  head := h0 + (ts.take (hexW2_cutPos h0 ts)).sum
  turns := ts.drop (hexW2_cutPos h0 ts)





noncomputable def hexW2_split (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop) :
    {ts // memD ts} → HexW2Half × HexW2Half :=
  fun d => (hexW2_lowerHalf a h0 d.1, hexW2_upperHalf a h0 d.1)




@[simp] theorem hexW2_split_fst_wt (a : ℂ) (h0 : ℤ) (x : ℝ) (memD : List ℤ → Prop)
    (d : {ts // memD ts}) :
    hexW2_halfWt x (hexW2_split a h0 memD d).1
      = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1)) :=
  rfl





@[simp] theorem hexW2_split_snd_wt (a : ℂ) (h0 : ℤ) (x : ℝ) (memD : List ℤ → Prop)
    (d : {ts // memD ts}) :
    hexW2_halfWt x (hexW2_split a h0 memD d).2
      = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
          (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1)) :=
  rfl








theorem hexW2_split_injective (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop) :
    Function.Injective (hexW2_split a h0 memD) := by
  intro d d' heq
  
  have hfst : (hexW2_split a h0 memD d).1 = (hexW2_split a h0 memD d').1 :=
    congrArg Prod.fst heq
  have hsnd : (hexW2_split a h0 memD d).2 = (hexW2_split a h0 memD d').2 :=
    congrArg Prod.snd heq
  have htake : d.1.take (hexW2_cutPos h0 d.1) = d'.1.take (hexW2_cutPos h0 d'.1) :=
    congrArg HexW2Half.turns hfst
  have hdrop : d.1.drop (hexW2_cutPos h0 d.1) = d'.1.drop (hexW2_cutPos h0 d'.1) :=
    congrArg HexW2Half.turns hsnd
  
  apply Subtype.ext
  calc d.1 = d.1.take (hexW2_cutPos h0 d.1) ++ d.1.drop (hexW2_cutPos h0 d.1) :=
        (List.take_append_drop _ _).symm
    _ = d'.1.take (hexW2_cutPos h0 d'.1) ++ d'.1.drop (hexW2_cutPos h0 d'.1) := by
        rw [htake, hdrop]
    _ = d'.1 := List.take_append_drop _ _

































noncomputable def hexW2_highestCut_chi_weightClosed (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable (hexW2_halfWt x)) :
    HexHighestCut x⁻¹ :=
  hexW2_highestCut a h0 hx memD HexW2Half (hexW2_halfWt x)
    (hexW2_halfWt_nonneg x (le_of_lt hx))
    (hexW2_split a h0 memD)
    (fun d => hexW2_split_fst_wt a h0 x memD d)
    (fun d => hexW2_split_snd_wt a h0 x memD d)
    (hexW2_split_injective a h0 memD)
    hDsum hBsum








noncomputable def hexW2_highestCut_chi_weightClosed_chi (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut_chi_weightClosed a h0 hexChiE_pos memD hDsum hBsum
















theorem hexW2_halves_displacement_split (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h0 ts
      = hexInfra_stepReSum (hexW2_lowerHalf a h0 ts).head (hexW2_lowerHalf a h0 ts).turns
        + hexInfra_stepReSum (hexW2_upperHalf a h0 ts).head (hexW2_upperHalf a h0 ts).turns := by
  show hexInfra_stepReSum h0 ts
    = hexInfra_stepReSum h0 (ts.take (hexW2_cutPos h0 ts))
      + hexInfra_stepReSum (h0 + (ts.take (hexW2_cutPos h0 ts)).sum)
          (ts.drop (hexW2_cutPos h0 ts))
  rw [hexW2_displacement_split h0 ts]
  congr 1
  
  rw [hexInfra_headAccum_eq_add_sum h0 (ts.take (hexW2_cutPos h0 ts))]










def hexW2_singleRight_memD : List ℤ → Prop := fun ts => ts = [(-1 : ℤ)]


def hexW2_singleRight_elt : {ts // hexW2_singleRight_memD ts} := ⟨[(-1 : ℤ)], rfl⟩








theorem hexW2_singleRight_split_wt (a : ℂ) (x : ℝ) :
    hexW2_halfWt x (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).1
        = hexSAWwt a 0 x ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)]))
      ∧ hexW2_halfWt x (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).2
        = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]))
            (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) x
            ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)])) :=
  ⟨hexW2_split_fst_wt a 0 x hexW2_singleRight_memD hexW2_singleRight_elt,
   hexW2_split_snd_wt a 0 x hexW2_singleRight_memD hexW2_singleRight_elt⟩




theorem hexW2_singleRight_split_injective (a : ℂ) :
    Function.Injective (hexW2_split a 0 hexW2_singleRight_memD) :=
  hexW2_split_injective a 0 hexW2_singleRight_memD

end StatMech.Universality
