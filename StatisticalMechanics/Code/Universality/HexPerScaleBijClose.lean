/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Code.Universality.HexW2Weight
import Code.Universality.HexSurgerySeams
import Code.Universality.HexStripCountsClose

namespace StatMech.Universality

open scoped BigOperators
open Filter Topology










open Classical in



noncomputable def hpb_splitEquiv (P Q : List ℤ → Prop) (hsub : ∀ ts, Q ts → P ts) :
    {ts // P ts} ≃ {ts // Q ts} ⊕ {ts // P ts ∧ ¬ Q ts} where
  toFun := fun x => if h : Q x.1 then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1, x.2, h⟩
  invFun := fun s => s.elim (fun q => ⟨q.1, hsub q.1 q.2⟩) (fun r => ⟨r.1, r.2.1⟩)
  left_inv := by rintro ⟨n, hn⟩; by_cases h : Q n <;> simp [h]
  right_inv := by
    rintro (⟨n, hn⟩ | ⟨n, hn1, hn2⟩)
    · simp [hn]
    · simp [hn2]











theorem hpb_tsum_setDiff (P Q : List ℤ → Prop) (w : List ℤ → ℝ)
    (hsub : ∀ ts, Q ts → P ts)
    (hsumP : Summable (fun n : {ts // P ts} => w n.1)) :
    (∑' d : {ts // P ts ∧ ¬ Q ts}, w d.1)
      = (∑' n : {ts // P ts}, w n.1) - (∑' n : {ts // Q ts}, w n.1) := by
  classical
  set g : ({ts // Q ts} ⊕ {ts // P ts ∧ ¬ Q ts}) → ℝ :=
    Sum.elim (fun q => w q.1) (fun d => w d.1) with hg
  have hcongr : ∀ x : {ts // P ts}, w x.1 = g (hpb_splitEquiv P Q hsub x) := by
    intro x
    change w x.1 = g (if h : Q x.1 then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1, x.2, h⟩)
    by_cases h : Q x.1 <;> simp [h, hg]
  have hsumG : Summable g := by
    have : Summable (fun x : {ts // P ts} => g (hpb_splitEquiv P Q hsub x)) :=
      hsumP.congr (fun x => hcongr x)
    exact ((hpb_splitEquiv P Q hsub).summable_iff (f := g)).mp this
  have hsumQ : Summable (fun q : {ts // Q ts} => w q.1) :=
    hsumG.comp_injective Sum.inl_injective
  have hsumD : Summable (fun d : {ts // P ts ∧ ¬ Q ts} => w d.1) :=
    hsumG.comp_injective Sum.inr_injective
  have key : (∑' n : {ts // P ts}, w n.1)
      = (∑' q : {ts // Q ts}, w q.1) + (∑' d : {ts // P ts ∧ ¬ Q ts}, w d.1) := by
    have h1 : (∑' n : {ts // P ts}, w n.1) = ∑' s, g s := by
      rw [← (hpb_splitEquiv P Q hsub).tsum_eq g]; exact tsum_congr hcongr
    rw [h1]; exact (HasSum.sum hsumQ.hasSum hsumD.hasSum).tsum_eq
  linarith [key]










noncomputable def hpb_lamS (a : ℂ) (h0 : ℤ) (x : ℝ) (memA : List ℤ → Prop) : ℝ :=
  ∑' d : {ts // memA ts}, hexSAWwt a h0 x d.1




noncomputable def hpb_upsS (a : ℂ) (h0 : ℤ) (x : ℝ) (memB : List ℤ → Prop) : ℝ :=
  ∑' b : {ts // memB ts}, hexSAWwt a h0 x b.1


theorem hpb_lamS_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (memA : List ℤ → Prop) :
    0 ≤ hpb_lamS a h0 x memA :=
  tsum_nonneg (fun d => hexSAWwt_nonneg a h0 hx d.1)


theorem hpb_upsS_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (memB : List ℤ → Prop) :
    0 ≤ hpb_upsS a h0 x memB :=
  tsum_nonneg (fun b => hexSAWwt_nonneg a h0 hx b.1)



















structure HexHalfClass (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop) where
  
  lower : {ts // memD ts} → {ts // memB ts}
  
  upper : {ts // memD ts} → {ts // memB ts}
  
  hlow : ∀ d, hexSAWwt a h0 x (lower d).1
    = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1))
  

  hupp : ∀ d, hexSAWwt a h0 x (upper d).1
    = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1))
  

  pair_inj : Function.Injective (fun d => (lower d, upper d))












noncomputable def hpb_cut (a : ℂ) (h0 : ℤ) (memD memB : List ℤ → Prop)
    (HC : HexHalfClass a h0 hexChiE memD memB)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut_chi a h0 memD {ts // memB ts}
    (fun b => hexSAWwt a h0 hexChiE b.1)
    (fun b => hexSAWwt_nonneg a h0 (le_of_lt hexChiE_pos) b.1)
    (fun d => (HC.lower d, HC.upper d))
    (fun d => HC.hlow d)
    (fun d => HC.hupp d)
    HC.pair_inj
    hDsum hBsum







theorem hpb_cut_wtB_sum (a : ℂ) (h0 : ℤ) (memD memB : List ℤ → Prop)
    (HC : HexHalfClass a h0 hexChiE memD memB)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    (∑' b, (hpb_cut a h0 memD memB HC hDsum hBsum).wtB b)
      = hpb_upsS a h0 hexChiE memB := rfl




theorem hpb_cut_wtγ_sum (a : ℂ) (h0 : ℤ) (memD memB : List ℤ → Prop)
    (HC : HexHalfClass a h0 hexChiE memD memB)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    (∑' d, (hpb_cut a h0 memD memB HC hDsum hBsum).wtγ d)
      = ∑' d : {ts // memD ts}, hexSAWwt a h0 hexChiE d.1 := rfl







theorem hpb_cut_wtγ_eq_diff (a : ℂ) (h0 : ℤ) (memA : ℕ → List ℤ → Prop) (memB : List ℤ → Prop)
    (v : ℕ) (hsub : ∀ ts, memA v ts → memA (v + 1) ts)
    (HC : HexHalfClass a h0 hexChiE (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB)
    (hDsum : Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
      hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1))
    (hAsum : Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a h0 hexChiE n.1)) :
    (∑' d, (hpb_cut a h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB HC hDsum hBsum).wtγ d)
      = hpb_lamS a h0 hexChiE (memA (v + 1)) - hpb_lamS a h0 hexChiE (memA v) := by
  rw [hpb_cut_wtγ_sum a h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB HC hDsum hBsum]
  unfold hpb_lamS
  exact hpb_tsum_setDiff (memA (v + 1)) (memA v) (hexSAWwt a h0 hexChiE) hsub hAsum






theorem hpb_cutB_eq {K : ℝ} (Cut : HexHighestCut K) (a : ℂ) (h0 : ℤ) (x : ℝ)
    (memB : List ℤ → Prop) (eB : Cut.B ≃ {ts // memB ts})
    (hwt : ∀ b, Cut.wtB b = hexSAWwt a h0 x (eB b).1) :
    (∑' b, Cut.wtB b) = hpb_upsS a h0 x memB := by
  unfold hpb_upsS
  rw [← eB.tsum_eq (fun b => hexSAWwt a h0 x b.1)]
  exact tsum_congr hwt
























theorem hpb_hexZ_chi_div (c : ℕ → ℝ) (a0 : ℂ) (h0 : ℤ)
    (memA memB : ℕ → List ℤ → Prop) (tau : ℕ → ℝ)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (HC : ∀ v, HexHalfClass a0 h0 hexChiE
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
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  set Cut : ℕ → HexHighestCut hexChiE⁻¹ := fun v =>
    hpb_cut a0 h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1))
      (HC v) (hDsum v) (hBsum v) with hCut
  
  have hCutD : ∀ v, 1 ≤ v →
      (∑' d, (Cut v).wtγ d)
        = hpb_lamS a0 h0 hexChiE (memA (v + 1)) - hpb_lamS a0 h0 hexChiE (memA v) := by
    intro v _
    exact hpb_cut_wtγ_eq_diff a0 h0 memA (memB (v + 1)) v (hsub v) (HC v)
      (hDsum v) (hBsum v) (hAsum v)
  
  have hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hpb_upsS a0 h0 hexChiE (memB (v + 1)) := by
    intro v _
    exact hpb_cut_wtB_sum a0 h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1))
      (HC v) (hDsum v) (hBsum v)
  
  exact hexZ_chi_div_seams_closed c
    (fun v => hpb_lamS a0 h0 hexChiE (memA v)) tau (fun v => hpb_upsS a0 h0 hexChiE (memB v))
    hbdry hlamMono hυpos
    (fun v => hpb_upsS_nonneg a0 h0 (le_of_lt hexChiE_pos) (memB v)) hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc
















theorem hpb_sidePhaseLock (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
    parafObservable region a h0 z σ x
        + parafObservable region a h0 (hsc_refl a h0 z) σ x
      = ((2 * Real.cos (σ * W) * hexClosed_countObs region a h0 z x : ℝ) : ℂ) :=
  hsc_sidePhaseLock_single region a h0 z σ x W hsym hdett














def hpb_emptyHalfClass (a : ℂ) (h0 : ℤ) (x : ℝ) (memB : List ℤ → Prop) :
    HexHalfClass a h0 x (fun _ => False) memB where
  lower := fun d => absurd d.2 (by simp)
  upper := fun d => absurd d.2 (by simp)
  hlow := fun d => absurd d.2 (by simp)
  hupp := fun d => absurd d.2 (by simp)
  pair_inj := fun d => absurd d.2 (by simp)



theorem hpb_emptyD_summable (a : ℂ) (h0 : ℤ) (x : ℝ) :
    Summable (fun d : {ts // (fun _ : List ℤ => False) ts} => hexSAWwt a h0 x d.1) := by
  have : IsEmpty {ts : List ℤ // (fun _ : List ℤ => False) ts} := ⟨fun d => d.2⟩
  exact summable_empty




theorem hpb_eD_empty_fires (a : ℂ) (h0 : ℤ) (x : ℝ) (P : List ℤ → Prop)
    (hsumP : Summable (fun n : {ts // P ts} => hexSAWwt a h0 x n.1)) :
    (∑' d : {ts // P ts ∧ ¬ P ts}, hexSAWwt a h0 x d.1)
      = hpb_lamS a h0 x P - hpb_lamS a h0 x P := by
  unfold hpb_lamS
  exact hpb_tsum_setDiff P P (hexSAWwt a h0 x) (fun _ h => h) hsumP






theorem hpb_eB_empty_fires (a : ℂ) (h0 : ℤ) (memB : List ℤ → Prop)
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    (∑' b, (hpb_cut a h0 (fun _ => False) memB
        (hpb_emptyHalfClass a h0 hexChiE memB) (hpb_emptyD_summable a h0 hexChiE) hBsum).wtB b)
      = hpb_upsS a h0 hexChiE memB :=
  hpb_cut_wtB_sum a h0 (fun _ => False) memB
    (hpb_emptyHalfClass a h0 hexChiE memB) (hpb_emptyD_summable a h0 hexChiE) hBsum









theorem hpb_data_satisfiable :
    ∃ (a0 : ℂ) (h0 : ℤ) (memA memB : ℕ → List ℤ → Prop),
      (∀ v ts, memA v ts → memA (v + 1) ts) ∧
      (∀ v, Nonempty (HexHalfClass a0 h0 hexChiE
        (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)))) ∧
      (∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
        hexSAWwt a0 h0 hexChiE d.1)) ∧
      (∀ v, Summable (fun b : {ts // memB (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1)) := by
  refine ⟨0, 0, (fun _ _ => False), (fun _ ts => ts = []), ?_, ?_, ?_, ?_⟩
  · intro _ _ h; exact h
  · intro v
    have heq : (fun ts => (fun _ : List ℤ => False) ts ∧ ¬ (fun _ : List ℤ => False) ts)
        = (fun _ : List ℤ => False) := by funext ts; simp
    rw [heq]; exact ⟨hpb_emptyHalfClass 0 0 hexChiE (fun ts => ts = [])⟩
  · intro v
    have heq : (fun ts => (fun _ : List ℤ => False) ts ∧ ¬ (fun _ : List ℤ => False) ts)
        = (fun _ : List ℤ => False) := by funext ts; simp
    rw [heq]; exact hpb_emptyD_summable 0 0 hexChiE
  · intro v
    haveI : Subsingleton {ts : List ℤ // ts = []} :=
      ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
    haveI : Finite {ts : List ℤ // ts = []} := Finite.of_subsingleton
    exact Summable.of_finite

end StatMech.Universality
