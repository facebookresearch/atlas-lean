/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.Count
public import Mathlib.Data.Set.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
private noncomputable def ac_cnt (ω : ℕ → Fin 3) (a : Fin 3) (i j : ℕ) : ℕ :=
  ((Finset.Ico i j).filter (fun k => ω k = a)).card

private theorem ac_cnt_split (ω : ℕ → Fin 3) (a : Fin 3) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    ac_cnt ω a i k = ac_cnt ω a i j + ac_cnt ω a j k := by
  unfold ac_cnt
  rw [← Finset.Ico_union_Ico_eq_Ico hij hjk, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive i j k)

private theorem ac_cnt_total (ω : ℕ → Fin 3) {i j : ℕ} :
    ac_cnt ω 0 i j + ac_cnt ω 1 i j + ac_cnt ω 2 i j = j - i := by
  have ne01 : (0 : Fin 3) ≠ 1 := by decide
  have ne02 : (0 : Fin 3) ≠ 2 := by decide
  have ne12 : (1 : Fin 3) ≠ 2 := by decide
  have d01 : Disjoint ((Finset.Ico i j).filter (fun k => ω k = 0))
      ((Finset.Ico i j).filter (fun k => ω k = 1)) := by
    rw [Finset.disjoint_left]
    intro k hk0 hk1
    rw [Finset.mem_filter] at hk0 hk1
    exact ne01 (hk0.2.symm.trans hk1.2)
  have d012 : Disjoint (((Finset.Ico i j).filter (fun k => ω k = 0)) ∪
      ((Finset.Ico i j).filter (fun k => ω k = 1)))
      ((Finset.Ico i j).filter (fun k => ω k = 2)) := by
    rw [Finset.disjoint_left]
    intro k hk01 hk2
    rw [Finset.mem_union] at hk01
    rw [Finset.mem_filter] at hk2
    refine hk01.elim (fun hk0 => ?_) (fun hk1 => ?_)
    · rw [Finset.mem_filter] at hk0
      exact ne02 (hk0.2.symm.trans hk2.2)
    · rw [Finset.mem_filter] at hk1
      exact ne12 (hk1.2.symm.trans hk2.2)
  have hunion : ((((Finset.Ico i j).filter (fun k => ω k = 0)) ∪
      ((Finset.Ico i j).filter (fun k => ω k = 1))) ∪
      ((Finset.Ico i j).filter (fun k => ω k = 2))) = Finset.Ico i j := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · intro hk
      refine hk.elim (fun hk01 => ?_) (fun hk2 => hk2.1)
      refine hk01.elim (fun hk0 => hk0.1) (fun hk1 => hk1.1)
    · intro h
      have tri : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
      refine (tri (ω k)).elim (fun h0 => Or.inl (Or.inl ⟨h, h0⟩)) (fun h12 => ?_)
      refine h12.elim (fun h1 => Or.inl (Or.inr ⟨h, h1⟩)) (fun h2 => Or.inr ⟨h, h2⟩)
  unfold ac_cnt
  rw [← Finset.card_union_of_disjoint d01, ← Finset.card_union_of_disjoint d012,
    hunion, Nat.card_Ico]

-- List total
private theorem ac_list_total (u : List (Fin 3)) :
    u.length = u.count 0 + u.count 1 + u.count 2 := by
  induction u with
  | nil => rfl
  | cons hd tl ih =>
    have tri : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    simp only [List.length_cons, List.count_cons]
    have e01 : ((0 : Fin 3) == 1) = false := rfl
    have e02 : ((0 : Fin 3) == 2) = false := rfl
    have e10 : ((1 : Fin 3) == 0) = false := rfl
    have e12 : ((1 : Fin 3) == 2) = false := rfl
    have e20 : ((2 : Fin 3) == 0) = false := rfl
    have e21 : ((2 : Fin 3) == 1) = false := rfl
    refine (tri hd).elim (fun h0 => ?_) (fun h12 => ?_)
    · subst h0; simp [e01, e02]; omega
    · refine h12.elim (fun h1 => ?_) (fun h2 => ?_)
      · subst h1; simp [e10, e12]; omega
      · subst h2; simp [e20, e21]; omega

-- In range-map form
private theorem ac_cnt_range (ω : ℕ → Fin 3) (a : Fin 3) (i L : ℕ) :
    ac_cnt ω a i (i + L) = ((List.range L).map (fun k => ω (i + k))).count a := by
  induction L generalizing i with
  | zero => simp [ac_cnt]
  | succ L ih =>
    have hsplit : Finset.Ico i (i + (L + 1)) =
        Finset.Ico i (i + L) ∪ Finset.Ico (i + L) (i + L + 1) := by
      have e : i + (L + 1) = i + L + 1 := by omega
      rw [e, Finset.Ico_union_Ico_eq_Ico] <;> omega
    have hsing : Finset.Ico (i + L) (i + L + 1) = {i + L} := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      constructor
      · intro h; obtain ⟨h1, h2⟩ := h; omega
      · intro h; subst h; exact ⟨le_refl _, Nat.lt_succ_self _⟩
    have hdisj : Disjoint ((Finset.Ico i (i + L)).filter (fun k => ω k = a))
        ((Finset.Ico (i + L) (i + L + 1)).filter (fun k => ω k = a)) :=
      Finset.disjoint_filter_filter
        (Finset.Ico_disjoint_Ico_consecutive i (i + L) (i + L + 1))
    have hcard1 : (((Finset.Ico (i + L) (i + L + 1)).filter
        (fun k => ω k = a))).card = (if ω (i + L) = a then 1 else 0) := by
      rw [hsing, Finset.filter_singleton]
      by_cases h : ω (i + L) = a <;> simp [h]
    have hmap : ((List.range (L + 1)).map (fun k => ω (i + k))) =
        ((List.range L).map (fun k => ω (i + k))) ++ [ω (i + L)] := by
      rw [List.range_succ, List.map_append]
      congr 1
    have hsplit' : ac_cnt ω a i (i + (L + 1)) =
        ac_cnt ω a i (i + L) + (if ω (i + L) = a then 1 else 0) := by
      unfold ac_cnt
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, hcard1]
    have hsingle : ([ω (i + L)].count a) = (if ω (i + L) = a then 1 else 0) := by
      by_cases h : ω (i + L) = a <;> simp [h]
    rw [hsplit', hmap, List.count_append, hsingle, ih]

private def ac_hImg : Fin 3 → List (Fin 3)
  | 0 => [0, 0, 2, 0, 0, 1]
  | 1 => [2, 1, 1, 0, 0, 1]
  | 2 => [2, 2, 0, 2, 2, 1]

private def ac_hAlt : Fin 3 → List (Fin 3)
  | 0 => [0, 0, 2, 0, 0, 1]
  | 1 => [0, 0, 1, 1, 2, 1]
  | 2 => [2, 2, 0, 2, 2, 1]

private def ac_img (c : Bool) (a : Fin 3) : List (Fin 3) :=
  if c then ac_hAlt a else ac_hImg a

private def ac_delta (n : ℕ) : Fin 3 :=
  if _h : n = 0 then 0
  else (ac_hImg (ac_delta (n / 6))).getD (n % 6) 0
termination_by n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

private theorem ac_delta_zero : ac_delta 0 = 0 := by
  conv_lhs => rw [ac_delta.eq_1]
  simp

private theorem ac_delta_unfold (q r : ℕ) (hr : r < 6) :
    ac_delta (6 * q + r) = (ac_hImg (ac_delta q)).getD r 0 := by
  by_cases h0 : 6 * q + r = 0
  · have hq : q = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hq; subst hr0
    simp only [Nat.mul_zero, Nat.add_zero, ac_delta_zero]
    decide
  · have e : 6 * q + r = r + 6 * q := by omega
    conv_lhs => rw [ac_delta.eq_1]
    rw [dite_eq_right h0, e, Nat.add_mul_div_left _ _ (show 0 < 6 by decide),
      Nat.div_eq_of_lt hr, Nat.zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hr]

private def ac_omega (b : ℕ → Bool) (n : ℕ) : Fin 3 :=
  (ac_img (b (n / 6)) (ac_delta (n / 6))).getD (n % 6) 0

private theorem ac_omega_unfold (b : ℕ → Bool) (q r : ℕ) (hr : r < 6) :
    ac_omega b (6 * q + r) = (ac_img (b q) (ac_delta q)).getD r 0 := by
  unfold ac_omega
  have e : 6 * q + r = r + 6 * q := by omega
  rw [e, Nat.add_mul_div_left _ _ (show 0 < 6 by decide),
    Nat.div_eq_of_lt hr, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hr]

private theorem ac_img_length : ∀ (c : Bool) (a : Fin 3), (ac_img c a).length = 6 := by
  decide

private theorem ac_img_count : ∀ (c : Bool) (a x : Fin 3),
    (ac_img c a).count x = (ac_hImg a).count x := by
  decide

-- M columns: count of a in hImg c is rows (4,2,1), (1,3,1), (1,1,4)
private theorem ac_M_entries : ((ac_hImg 0).count 0 = 4) ∧ ((ac_hImg 1).count 0 = 2) ∧
    ((ac_hImg 2).count 0 = 1) ∧ ((ac_hImg 0).count 1 = 1) ∧
    ((ac_hImg 1).count 1 = 3) ∧ ((ac_hImg 2).count 1 = 1) ∧
    ((ac_hImg 0).count 2 = 1) ∧ ((ac_hImg 1).count 2 = 1) ∧
    ((ac_hImg 2).count 2 = 4) := by
  decide

private theorem ac_block_zero (ω δ : ℕ → Fin 3) (blk : ℕ → List (Fin 3))
    (M : Fin 3 → Fin 3 → ℕ)
    (hlen : ∀ q, (blk q).length = 6)
    (hω : ∀ q r, r < 6 → ω (6 * q + r) = (blk q).getD r 0)
    (hM : ∀ a q, (blk q).count a = M a (δ q))
    (a : Fin 3) (q : ℕ) :
    ac_cnt ω a 0 (6 * q) = ∑ c : Fin 3, M a c * ac_cnt δ c 0 q := by
  induction q with
  | zero =>
    have hz : ∀ c : Fin 3, ac_cnt δ c 0 0 = 0 := by
      intro c
      simp only [ac_cnt, Finset.Ico_self, Finset.filter_empty, Finset.card_empty]
    simp only [ac_cnt, Finset.Ico_self, Finset.filter_empty,
      Finset.card_empty, mul_zero, Finset.sum_const_zero]
  | succ q ih =>
    have hδstep : ∀ c : Fin 3, ac_cnt δ c 0 (q + 1) =
        ac_cnt δ c 0 q + (if δ q = c then 1 else 0) := by
      intro c
      have h := ac_cnt_split (ω := δ) (a := c) (i := 0) (j := q) (k := q + 1)
        (Nat.zero_le q) (Nat.le_succ q)
      rw [h]
      congr 1
      simp only [ac_cnt]
      have hsing : Finset.Ico q (q + 1) = {q} := by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        constructor
        · intro hk; obtain ⟨h1, h2⟩ := hk; omega
        · intro hk; subst hk; exact ⟨le_refl _, Nat.lt_succ_self _⟩
      rw [hsing, Finset.filter_singleton]
      by_cases hc : δ q = c <;> simp [hc]
    have hmap : ((List.range 6).map (fun k => ω (6 * q + k))) = blk q := by
      apply List.ext_getElem
      · rw [List.length_map, List.length_range, hlen q]
      · intro i h1 h2
        have hi6 : i < 6 := hlen q ▸ h2
        rw [List.getElem_map,
          List.getElem_range (by simpa [List.length_map] using h1),
          hω q i hi6, List.getD_eq_getElem _ _ h2]
    have hwindow : ac_cnt ω a (6 * q) (6 * q + 6) = (blk q).count a := by
      have h := ac_cnt_range ω a (6 * q) 6
      rw [h, hmap]
    have hsum : (∑ c : Fin 3, M a c * (if δ q = c then 1 else 0)) = M a (δ q) := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    have h6q : 6 * (q + 1) = 6 * q + 6 := by ring
    have hsp := ac_cnt_split (ω := ω) (a := a) (i := 0) (j := 6 * q)
      (k := 6 * q + 6) (by omega) (by omega)
    rw [h6q, hsp, ih, hwindow, hM a q]
    simp only [hδstep, mul_add, Finset.sum_add_distrib]
    rw [hsum]

private theorem ac_block_full (ω δ : ℕ → Fin 3) (blk : ℕ → List (Fin 3))
    (M : Fin 3 → Fin 3 → ℕ)
    (hlen : ∀ q, (blk q).length = 6)
    (hω : ∀ q r, r < 6 → ω (6 * q + r) = (blk q).getD r 0)
    (hM : ∀ a q, (blk q).count a = M a (δ q))
    (a : Fin 3) (q r : ℕ) (hr : r < 6) :
    ac_cnt ω a 0 (6 * q + r) =
      (∑ c : Fin 3, M a c * ac_cnt δ c 0 q) + ((blk q).take r).count a := by
  have hmap2 : ((List.range r).map (fun k => ω (6 * q + k))) =
      (blk q).take r := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, List.length_take, hlen q]
      omega
    · intro i h1 h2
      have hir : i < r := by simpa [List.length_map, List.length_range] using h1
      have hi6 : i < 6 := by omega
      have h2' : i < (blk q).length := by
        rw [hlen q]; exact hi6
      have htb : i < ((blk q).take r).length := by
        have htblen : ((blk q).take r).length = r := by
          rw [List.length_take, hlen q]
          omega
        omega
      rw [List.getElem_map,
        List.getElem_range (by simpa [List.length_map] using h1),
        hω q i hi6]
      simp only [List.getElem_take]
      exact List.getD_eq_getElem _ _ h2'
  have hsp := ac_cnt_split (ω := ω) (a := a) (i := 0) (j := 6 * q)
    (k := 6 * q + r) (by omega) (by omega)
  rw [hsp, ac_block_zero ω δ blk M hlen hω hM a q]
  congr 1
  have h := ac_cnt_range ω a (6 * q) r
  rw [h, hmap2]

-- Adjugate identities
private theorem ac_adj_mul {x0 x1 x2 v0 v1 v2 : ℤ}
    (h0 : 4 * x0 + 2 * x1 + x2 = v0)
    (h1 : x0 + 3 * x1 + x2 = v1)
    (h2 : x0 + x1 + 4 * x2 = v2) :
    11 * v0 - 7 * v1 - v2 = 36 * x0 ∧
    -3 * v0 + 15 * v1 - 3 * v2 = 36 * x1 ∧
    -2 * v0 - 2 * v1 + 10 * v2 = 36 * x2 := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

private theorem ac_block_eq_map (ω : ℕ → Fin 3) (B n : ℕ)
    (W : List (Fin 3)) (hW : W = List.ofFn (fun k : Fin n => ω (B + k)))
    (pre blk post : List (Fin 3)) (off L : ℕ)
    (hfac : W = pre ++ (blk ++ post))
    (hoff : off = B + pre.length) (hL : L = blk.length) :
    (List.range L).map (fun k => ω (off + k)) = blk := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hL]
  · intro i h1 h2
    have hiL : i < L := by simpa [List.length_map, List.length_range] using h1
    have hiB : i < blk.length := by omega
    have hfin : off + i = B + (pre.length + i) := by omega
    have hbp : i < (blk ++ post).length := by
      rw [List.length_append]; omega
    have hpre : pre.length + i < (pre ++ (blk ++ post)).length := by
      rw [List.length_append, List.length_append]; omega
    have hWlen : pre.length + i < W.length := by rw [hfac]; exact hpre
    have hWi : pre.length + i < n := by
      have hWlen2 : W.length = n := by rw [hW, List.length_ofFn]
      omega
    have hlen : pre.length + i <
        (List.ofFn (fun k : Fin n => ω (B + k))).length := by
      rw [List.length_ofFn]; exact hWi
    rw [List.getElem_map,
      List.getElem_range (by simpa [List.length_map] using h1)]
    change ω (off + i) = blk[i]'h2
    have e1 : blk[i]'hiB = (blk ++ post)[i]'hbp :=
      (List.getElem_append_left hiB).symm
    have e2 : (blk ++ post)[i]'hbp =
        (pre ++ (blk ++ post))[pre.length + i]'hpre := by
      have h := List.getElem_append_right (as := pre) (bs := blk ++ post)
        (i := pre.length + i) (h₁ := show pre.length ≤ pre.length + i by omega)
        (h₂ := hpre)
      have hsub : pre.length + i - pre.length = i := by omega
      simp only [hsub] at h
      exact h.symm
    have e3 : (pre ++ (blk ++ post))[pre.length + i]'hpre =
        W[pre.length + i]'hWlen := by
      have o : (pre ++ (blk ++ post))[pre.length + i]? = W[pre.length + i]? := by
        rw [hfac]
      rw [List.getElem?_eq_getElem hpre, List.getElem?_eq_getElem hWlen] at o
      exact Option.some_inj.mp o
    have e5 : W[pre.length + i]'hWlen =
        (List.ofFn (fun k : Fin n => ω (B + k)))[pre.length + i]'hlen := by
      have o : W[pre.length + i]? =
          (List.ofFn (fun k : Fin n => ω (B + k)))[pre.length + i]? := by
        rw [hW]
      rw [List.getElem?_eq_getElem hWlen, List.getElem?_eq_getElem hlen] at o
      exact Option.some_inj.mp o
    have e4 : (List.ofFn (fun k : Fin n => ω (B + k)))[pre.length + i]'hlen =
        ω (B + (pre.length + i)) := by
      rw [List.getElem_ofFn hlen]
    rw [e1, e2, e3, e5, e4, hfin]

-- Main: list factorization gives window-count equalities
private theorem ac_list_factor_bridge (ω : ℕ → Fin 3) (B n : ℕ)
    (W : List (Fin 3)) (hW : W = List.ofFn (fun k : Fin n => ω (B + k)))
    (p x y z s : List (Fin 3))
    (hfac : W = p ++ x ++ y ++ z ++ s)
    (hx : x ≠ []) (_hy : y ≠ []) (_hz : z ≠ [])
    (hxy : ∀ a : Fin 3, x.count a = y.count a)
    (hyz : ∀ a : Fin 3, y.count a = z.count a) :
    1 ≤ x.length ∧ y.length = x.length ∧ z.length = x.length ∧
      (∀ a : Fin 3,
        ac_cnt ω a (B + p.length) (B + p.length + x.length) =
          ac_cnt ω a (B + (p.length + x.length))
            (B + (p.length + x.length) + y.length) ∧
        ac_cnt ω a (B + (p.length + x.length))
            (B + (p.length + x.length) + y.length) =
          ac_cnt ω a (B + ((p.length + x.length) + y.length))
            (B + ((p.length + x.length) + y.length) + z.length)) := by
  have hlen : x.length = y.length ∧ y.length = z.length := by
    have hx2 := ac_list_total x
    have hy2 := ac_list_total y
    have hz2 := ac_list_total z
    have exy : x.count 0 + x.count 1 + x.count 2 =
        y.count 0 + y.count 1 + y.count 2 := by
      rw [hxy 0, hxy 1, hxy 2]
    have eyz : y.count 0 + y.count 1 + y.count 2 =
        z.count 0 + z.count 1 + z.count 2 := by
      rw [hyz 0, hyz 1, hyz 2]
    constructor <;> omega
  have hℓ : 1 ≤ x.length := by
    by_contra hcon
    have hz0 : x.length = 0 := by omega
    exact hx (List.length_eq_zero_iff.mp hz0)
  have hfac_x : W = p ++ (x ++ ((y ++ z) ++ s)) := by
    simp only [hfac, List.append_assoc]
  have hfac_y : W = (p ++ x) ++ (y ++ ((z ++ s))) := by
    simp only [hfac, List.append_assoc]
  have hfac_z : W = ((p ++ x) ++ y) ++ (z ++ s) := by
    simp only [hfac, List.append_assoc]
  have hxmap : (List.range x.length).map (fun k => ω ((B + p.length) + k)) = x :=
    ac_block_eq_map ω B n W hW p x ((y ++ z) ++ s) (B + p.length) x.length
      hfac_x rfl rfl
  have hymap : (List.range y.length).map
      (fun k => ω ((B + (p.length + x.length)) + k)) = y :=
    ac_block_eq_map ω B n W hW (p ++ x) y (z ++ s)
      (B + (p.length + x.length)) y.length hfac_y
      (by rw [List.length_append]) rfl
  have hzmap : (List.range z.length).map
      (fun k => ω ((B + ((p.length + x.length) + y.length)) + k)) = z :=
    ac_block_eq_map ω B n W hW ((p ++ x) ++ y) z s
      (B + ((p.length + x.length) + y.length)) z.length hfac_z
      (by rw [List.length_append, List.length_append]) rfl
  have cx : ∀ a : Fin 3, ac_cnt ω a (B + p.length) (B + p.length + x.length) =
      x.count a := by
    intro a
    have h := ac_cnt_range ω a (B + p.length) x.length
    rw [hxmap] at h
    exact h
  have cy : ∀ a : Fin 3, ac_cnt ω a (B + (p.length + x.length))
      (B + (p.length + x.length) + y.length) = y.count a := by
    intro a
    have h := ac_cnt_range ω a (B + (p.length + x.length)) y.length
    rw [hymap] at h
    exact h
  have cz : ∀ a : Fin 3, ac_cnt ω a (B + ((p.length + x.length) + y.length))
      (B + ((p.length + x.length) + y.length) + z.length) = z.count a := by
    intro a
    have h := ac_cnt_range ω a (B + ((p.length + x.length) + y.length)) z.length
    rw [hzmap] at h
    exact h
  refine ⟨hℓ, hlen.1.symm, hlen.2.symm.trans hlen.1.symm, fun a => ?_⟩
  constructor
  · rw [cx a, cy a]
    exact hxy a
  · rw [cy a, cz a]
    exact hyz a

private def ac_pre (u : List (Fin 3)) (r : ℕ) : ℤ × ℤ × ℤ :=
  ((u.take r).count 0, (u.take r).count 1, (u.take r).count 2)

-- images table: true = choice, false = plain
private def ac_imgs (choice : Bool) : Fin 3 → List (List (Fin 3))
  | 0 => [ac_hImg 0]
  | 1 => if choice then [ac_hImg 1, ac_hAlt 1] else [ac_hImg 1]
  | 2 => [ac_hImg 2]

-- opts(imgs, α): (α', prefix-vector) with u[r] = α
private def ac_opts (choice : Bool) (α : Fin 3) : List (Fin 3 × (ℤ × ℤ × ℤ)) :=
  (List.finRange 3).flatMap (fun α' =>
    (ac_imgs choice α').flatMap (fun u =>
      (List.range 6).filterMap (fun r =>
        if u.getD r 0 = α then some (α', ac_pre u r) else none)))

-- adjugate times vector
private def ac_adjMul (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (11 * v.1 - 7 * v.2.1 - v.2.2,
   -3 * v.1 + 15 * v.2.1 - 3 * v.2.2,
   -2 * v.1 - 2 * v.2.1 + 10 * v.2.2)

-- parent of template under options; none if not divisible
private def ac_parent (t : (Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)))
    (o : (Fin 3 × (ℤ × ℤ × ℤ)) × (Fin 3 × (ℤ × ℤ × ℤ)) ×
         (Fin 3 × (ℤ × ℤ × ℤ)) × (Fin 3 × (ℤ × ℤ × ℤ))) :
    Option ((Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) :=
  let (_α, d) := t
  let d1 := d.1; let d2 := d.2
  let e0 := o.1.2; let e1 := o.2.1.2; let e2 := o.2.2.1.2; let e3 := o.2.2.2.2
  let v1 : ℤ × ℤ × ℤ :=
    (d1.1 - e0.1 + 2 * e1.1 - e2.1, d1.2.1 - e0.2.1 + 2 * e1.2.1 - e2.2.1,
     d1.2.2 - e0.2.2 + 2 * e1.2.2 - e2.2.2)
  let v2 : ℤ × ℤ × ℤ :=
    (d2.1 - e1.1 + 2 * e2.1 - e3.1, d2.2.1 - e1.2.1 + 2 * e2.2.1 - e3.2.1,
     d2.2.2 - e1.2.2 + 2 * e2.2.2 - e3.2.2)
  let w1 := ac_adjMul v1; let w2 := ac_adjMul v2
  if w1.1 % 36 = 0 ∧ w1.2.1 % 36 = 0 ∧ w1.2.2 % 36 = 0 ∧
     w2.1 % 36 = 0 ∧ w2.2.1 % 36 = 0 ∧ w2.2.2 % 36 = 0 then
    some ((o.1.1, o.2.1.1, o.2.2.1.1, o.2.2.2.1),
      ((w1.1 / 36, w1.2.1 / 36, w1.2.2 / 36),
       (w2.1 / 36, w2.2.1 / 36, w2.2.2 / 36)))
  else none

-- all parents of t under choice/plain options
private def ac_parents (choice : Bool)
    (t : (Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) :
    List ((Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) :=
  let (α, _) := t
  let o0 := ac_opts choice α.1
  let o1 := ac_opts choice α.2.1
  let o2 := ac_opts choice α.2.2.1
  let o3 := ac_opts choice α.2.2.2
  (o0.flatMap (fun a0 => o1.flatMap (fun a1 => o2.flatMap (fun a2 =>
    o3.filterMap (fun a3 => ac_parent t (a0, a1, a2, a3)))))).eraseDups

private abbrev ac_Tpl : Type :=
  (Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))

-- zero templates over all 81 letter-quadruples
private def ac_zeroTemplates : List ((Fin 3 × Fin 3 × Fin 3 × Fin 3) ×
    ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) :=
  (List.finRange 3).flatMap (fun a0 => (List.finRange 3).flatMap (fun a1 =>
    (List.finRange 3).flatMap (fun a2 => (List.finRange 3).map (fun a3 =>
      ((a0, a1, a2, a3), ((0, 0, 0), (0, 0, 0)))))))

-- T pasted as a literal (closure of choice-parents of the 81 zero templates
-- under plain parents; sizes 189 → 191 → 191). Pasting avoids recomputing
-- the closure in the kernel on every membership test.
set_option maxHeartbeats 2000000 in
-- Elaborating the 191-element literal needs ~10x the default heartbeat budget.
private def ac_T : List ac_Tpl :=
  [
    ((0, 0, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 0, 1), ((0, 0, 0), (1, -1, 0))),
    ((0, 0, 1, 0), ((1, -1, 0), (-2, 2, 0))),
    ((0, 0, 1, 1), ((1, -1, 0), (-1, 1, 0))),
    ((0, 1, 0, 0), ((-2, 2, 0), (1, -1, 0))),
    ((0, 1, 0, 1), ((-2, 2, 0), (2, -2, 0))),
    ((0, 1, 1, 0), ((-1, 1, 0), (-1, 1, 0))),
    ((0, 1, 1, 1), ((-1, 1, 0), (0, 0, 0))),
    ((1, 0, 0, 0), ((1, -1, 0), (0, 0, 0))),
    ((1, 0, 0, 1), ((1, -1, 0), (1, -1, 0))),
    ((1, 0, 1, 0), ((2, -2, 0), (-2, 2, 0))),
    ((1, 0, 1, 1), ((2, -2, 0), (-1, 1, 0))),
    ((1, 1, 0, 0), ((-1, 1, 0), (1, -1, 0))),
    ((1, 1, 0, 1), ((-1, 1, 0), (2, -2, 0))),
    ((1, 1, 1, 0), ((0, 0, 0), (-1, 1, 0))),
    ((1, 1, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 0, 1), ((-1, 0, 1), (1, -1, 0))),
    ((0, 2, 0, 2), ((-1, 0, 1), (1, 0, -1))),
    ((0, 2, 1, 1), ((0, -1, 1), (-1, 1, 0))),
    ((0, 2, 1, 2), ((0, -1, 1), (-1, 2, -1))),
    ((1, 0, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 0, 1), ((-1, 0, 1), (1, -1, 0))),
    ((1, 2, 0, 2), ((-1, 0, 1), (1, 0, -1))),
    ((1, 2, 1, 1), ((0, -1, 1), (-1, 1, 0))),
    ((1, 2, 1, 2), ((0, -1, 1), (-1, 2, -1))),
    ((0, 0, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 1, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 0, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 1, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 1, 1), ((-1, 0, 1), (1, 0, -1))),
    ((1, 2, 1, 1), ((0, -1, 1), (1, 0, -1))),
    ((0, 2, 1, 2), ((-1, 0, 1), (1, 0, -1))),
    ((1, 2, 1, 2), ((0, -1, 1), (1, 0, -1))),
    ((0, 2, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((0, 2, 0, 1), ((-1, 0, 1), (1, 0, -1))),
    ((1, 2, 0, 1), ((0, -1, 1), (1, 0, -1))),
    ((0, 2, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((1, 2, 0, 2), ((0, -1, 1), (1, 0, -1))),
    ((1, 2, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((0, 0, 0, 2), ((0, 0, 0), (1, 0, -1))),
    ((0, 0, 1, 2), ((1, -1, 0), (-1, 2, -1))),
    ((0, 0, 2, 0), ((1, 0, -1), (-2, 0, 2))),
    ((0, 0, 2, 1), ((1, 0, -1), (-1, -1, 2))),
    ((0, 0, 2, 2), ((1, 0, -1), (-1, 0, 1))),
    ((0, 1, 0, 2), ((-2, 2, 0), (2, -1, -1))),
    ((0, 1, 1, 2), ((-1, 1, 0), (0, 1, -1))),
    ((0, 1, 2, 0), ((-1, 2, -1), (-1, -1, 2))),
    ((0, 1, 2, 1), ((-1, 2, -1), (0, -2, 2))),
    ((0, 1, 2, 2), ((-1, 2, -1), (0, -1, 1))),
    ((0, 2, 0, 0), ((-2, 0, 2), (1, 0, -1))),
    ((0, 2, 0, 1), ((-2, 0, 2), (2, -1, -1))),
    ((0, 2, 0, 2), ((-2, 0, 2), (2, 0, -2))),
    ((0, 2, 1, 0), ((-1, -1, 2), (-1, 2, -1))),
    ((0, 2, 1, 1), ((-1, -1, 2), (0, 1, -1))),
    ((0, 2, 1, 2), ((-1, -1, 2), (0, 2, -2))),
    ((0, 2, 2, 0), ((-1, 0, 1), (-1, 0, 1))),
    ((0, 2, 2, 1), ((-1, 0, 1), (0, -1, 1))),
    ((0, 2, 2, 2), ((-1, 0, 1), (0, 0, 0))),
    ((1, 0, 0, 2), ((1, -1, 0), (1, 0, -1))),
    ((1, 0, 1, 2), ((2, -2, 0), (-1, 2, -1))),
    ((1, 0, 2, 0), ((2, -1, -1), (-2, 0, 2))),
    ((1, 0, 2, 1), ((2, -1, -1), (-1, -1, 2))),
    ((1, 0, 2, 2), ((2, -1, -1), (-1, 0, 1))),
    ((1, 1, 0, 2), ((-1, 1, 0), (2, -1, -1))),
    ((1, 1, 1, 2), ((0, 0, 0), (0, 1, -1))),
    ((1, 1, 2, 0), ((0, 1, -1), (-1, -1, 2))),
    ((1, 1, 2, 1), ((0, 1, -1), (0, -2, 2))),
    ((1, 1, 2, 2), ((0, 1, -1), (0, -1, 1))),
    ((1, 2, 0, 0), ((-1, -1, 2), (1, 0, -1))),
    ((1, 2, 0, 1), ((-1, -1, 2), (2, -1, -1))),
    ((1, 2, 0, 2), ((-1, -1, 2), (2, 0, -2))),
    ((1, 2, 1, 0), ((0, -2, 2), (-1, 2, -1))),
    ((1, 2, 1, 1), ((0, -2, 2), (0, 1, -1))),
    ((1, 2, 1, 2), ((0, -2, 2), (0, 2, -2))),
    ((1, 2, 2, 0), ((0, -1, 1), (-1, 0, 1))),
    ((1, 2, 2, 1), ((0, -1, 1), (0, -1, 1))),
    ((1, 2, 2, 2), ((0, -1, 1), (0, 0, 0))),
    ((2, 0, 0, 0), ((1, 0, -1), (0, 0, 0))),
    ((2, 0, 0, 1), ((1, 0, -1), (1, -1, 0))),
    ((2, 0, 0, 2), ((1, 0, -1), (1, 0, -1))),
    ((2, 0, 1, 0), ((2, -1, -1), (-2, 2, 0))),
    ((2, 0, 1, 1), ((2, -1, -1), (-1, 1, 0))),
    ((2, 0, 1, 2), ((2, -1, -1), (-1, 2, -1))),
    ((2, 0, 2, 0), ((2, 0, -2), (-2, 0, 2))),
    ((2, 0, 2, 1), ((2, 0, -2), (-1, -1, 2))),
    ((2, 0, 2, 2), ((2, 0, -2), (-1, 0, 1))),
    ((2, 1, 0, 0), ((-1, 2, -1), (1, -1, 0))),
    ((2, 1, 0, 1), ((-1, 2, -1), (2, -2, 0))),
    ((2, 1, 0, 2), ((-1, 2, -1), (2, -1, -1))),
    ((2, 1, 1, 0), ((0, 1, -1), (-1, 1, 0))),
    ((2, 1, 1, 1), ((0, 1, -1), (0, 0, 0))),
    ((2, 1, 1, 2), ((0, 1, -1), (0, 1, -1))),
    ((2, 1, 2, 0), ((0, 2, -2), (-1, -1, 2))),
    ((2, 1, 2, 1), ((0, 2, -2), (0, -2, 2))),
    ((2, 1, 2, 2), ((0, 2, -2), (0, -1, 1))),
    ((2, 2, 0, 0), ((-1, 0, 1), (1, 0, -1))),
    ((2, 2, 0, 1), ((-1, 0, 1), (2, -1, -1))),
    ((2, 2, 0, 2), ((-1, 0, 1), (2, 0, -2))),
    ((2, 2, 1, 0), ((0, -1, 1), (-1, 2, -1))),
    ((2, 2, 1, 1), ((0, -1, 1), (0, 1, -1))),
    ((2, 2, 1, 2), ((0, -1, 1), (0, 2, -2))),
    ((2, 2, 2, 0), ((0, 0, 0), (-1, 0, 1))),
    ((2, 2, 2, 1), ((0, 0, 0), (0, -1, 1))),
    ((1, 1, 2, 0), ((1, 0, -1), (-1, 0, 1))),
    ((1, 1, 2, 1), ((1, 0, -1), (0, -1, 1))),
    ((1, 0, 2, 0), ((1, 0, -1), (-1, 0, 1))),
    ((1, 0, 2, 1), ((1, 0, -1), (0, -1, 1))),
    ((1, 0, 2, 0), ((1, -1, 0), (-1, 0, 1))),
    ((1, 0, 2, 1), ((1, -1, 0), (-1, 0, 1))),
    ((1, 1, 2, 0), ((-1, 1, 0), (0, -1, 1))),
    ((1, 1, 2, 1), ((-1, 1, 0), (0, -1, 1))),
    ((2, 0, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 2, 0), ((1, 0, -1), (-1, 0, 1))),
    ((2, 0, 2, 1), ((1, 0, -1), (-1, 0, 1))),
    ((2, 1, 2, 0), ((-1, 2, -1), (0, -1, 1))),
    ((2, 1, 2, 1), ((-1, 2, -1), (0, -1, 1))),
    ((2, 0, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 2, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 1, 2, 0), ((1, 0, -1), (-1, 0, 1))),
    ((2, 1, 2, 1), ((1, 0, -1), (0, -1, 1))),
    ((2, 2, 0, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 0, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 1, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 1, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 0, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 1, 2), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 2, 0), ((0, 0, 0), (0, 0, 0))),
    ((2, 2, 2, 1), ((0, 0, 0), (0, 0, 0))),
    ((2, 0, 2, 1), ((1, 0, -1), (0, -1, 1))),
    ((1, 2, 1, 2), ((1, -2, 1), (-1, 2, -1))),
    ((2, 1, 2, 1), ((-1, 2, -1), (1, -2, 1))),
  ]

-- CLOSED checker (v1-pruned)
private def ac_closedCheck : Bool :=
  ac_T.all (fun t =>
    let o0 := ac_opts false t.1.1
    let o1 := ac_opts false t.1.2.1
    let o2 := ac_opts false t.1.2.2.1
    let o3 := ac_opts false t.1.2.2.2
    o0.all (fun a0 => o1.all (fun a1 => o2.all (fun a2 =>
      let v1 : ℤ × ℤ × ℤ :=
        (t.2.1.1 - a0.2.1 + 2 * a1.2.1 - a2.2.1,
         t.2.1.2.1 - a0.2.2.1 + 2 * a1.2.2.1 - a2.2.2.1,
         t.2.1.2.2 - a0.2.2.2 + 2 * a1.2.2.2 - a2.2.2.2)
      let w1 := ac_adjMul v1
      if w1.1 % 36 = 0 ∧ w1.2.1 % 36 = 0 ∧ w1.2.2 % 36 = 0 then
        o3.all (fun a3 =>
          match ac_parent t (a0, a1, a2, a3) with
          | none => true
          | some p => ac_T.contains p)
      else true))))

private def ac_zeroCheck : Bool :=
  ac_zeroTemplates.all (fun t =>
    let o0 := ac_opts true t.1.1
    let o1 := ac_opts true t.1.2.1
    let o2 := ac_opts true t.1.2.2.1
    let o3 := ac_opts true t.1.2.2.2
    o0.all (fun a0 => o1.all (fun a1 => o2.all (fun a2 =>
      let v1 : ℤ × ℤ × ℤ :=
        (t.2.1.1 - a0.2.1 + 2 * a1.2.1 - a2.2.1,
         t.2.1.2.1 - a0.2.2.1 + 2 * a1.2.2.1 - a2.2.2.1,
         t.2.1.2.2 - a0.2.2.2 + 2 * a1.2.2.2 - a2.2.2.2)
      let w1 := ac_adjMul v1
      if w1.1 % 36 = 0 ∧ w1.2.1 % 36 = 0 ∧ w1.2.2 % 36 = 0 then
        o3.all (fun a3 =>
          match ac_parent t (a0, a1, a2, a3) with
          | none => true
          | some p => ac_T.contains p)
      else true))))

-- Parikh vector of u on [i,j) as integers
private def ac_pu (u : List (Fin 3)) (i j : ℕ) : ℤ × ℤ × ℤ :=
  let s := (u.drop i).take (j - i)
  (s.count 0, s.count 1, s.count 2)

private def ac_baseCheck : Bool :=
  (List.finRange 3).all (fun a => (List.finRange 3).all (fun b =>
    let u := ac_hImg a ++ ac_hImg b
    (List.range 12).all (fun p0 => (List.range 12).all (fun p1 =>
      (List.range 12).all (fun p2 => (List.range 12).all (fun p3 =>
        if p0 ≤ p1 ∧ p1 ≤ p2 ∧ p2 ≤ p3 ∧ p0 ≤ 5 ∧ 1 ≤ p3 - p0 ∧ p3 - p0 ≤ 5 then
          let q01 := ac_pu u p0 p1
          let q12 := ac_pu u p1 p2
          let q23 := ac_pu u p2 p3
          let t : ac_Tpl := ((u.getD p0 0, u.getD p1 0, u.getD p2 0, u.getD p3 0),
            ((q12.1 - q01.1, q12.2.1 - q01.2.1, q12.2.2 - q01.2.2),
             (q23.1 - q12.1, q23.2.1 - q12.2.1, q23.2.2 - q12.2.2)))
          !(ac_T.contains t)
        else true))))))

private def ac_noaaCheck : Bool :=
  (List.finRange 3).all (fun a => (List.finRange 3).all (fun b =>
    [false, true].all (fun c => [false, true].all (fun c' =>
      let u := (if c then ac_hAlt a else ac_hImg a) ++
               (if c' then ac_hAlt b else ac_hImg b)
      (List.range 10).all (fun i =>
        decide (¬ (u.getD i 0 = u.getD (i + 1) 0 ∧
                   u.getD (i + 1) 0 = u.getD (i + 2) 0)))))))

-- Arithmetic: block-index monotonicity and span descent
private theorem ac_div_mono {i j : ℕ} (h : i ≤ j) : i / 6 ≤ j / 6 :=
  Nat.div_le_div_right h

private theorem ac_span_descent {i0 i3 : ℕ} (h : 6 ≤ i3 - i0) :
    1 ≤ i3 / 6 - i0 / 6 ∧ i3 / 6 - i0 / 6 < i3 - i0 := by
  constructor <;> omega

-- Verified option-table sizes (match ROUTE)
private theorem ac_opts_len0 : (ac_opts false 0).length = 7 := by decide
private theorem ac_opts_len1 : (ac_opts false 1).length = 5 := by decide
private theorem ac_opts_len2 : (ac_opts false 2).length = 6 := by decide
private theorem ac_pre_ex : ac_pre (ac_hImg 0) 3 = (2, 0, 1) := by decide

-- Holds (kernel check)
private theorem ac_noaaCheck_ok : ac_noaaCheck = true := by decide

-- N6(a,b,c): `#eval` returns true for each; plain `decide` exceeds the
-- elaborator heartbeat budget, so evaluate in the kernel instead.
private theorem ac_closedCheck_ok : ac_closedCheck = true := by
  decide +kernel
private theorem ac_zeroCheck_ok : ac_zeroCheck = true := by
  decide +kernel
private theorem ac_baseCheck_ok : ac_baseCheck = true := by
  decide +kernel

-- Parikh difference triple over two consecutive windows
private noncomputable def ac_pdiff (ω : ℕ → Fin 3) (i j k : ℕ) : ℤ × ℤ × ℤ :=
  ((ac_cnt ω 0 j k : ℤ) - (ac_cnt ω 0 i j : ℤ),
   (ac_cnt ω 1 j k : ℤ) - (ac_cnt ω 1 i j : ℤ),
   (ac_cnt ω 2 j k : ℤ) - (ac_cnt ω 2 i j : ℤ))

-- template realization at i0 ≤ i1 ≤ i2 ≤ i3
private def ac_realizes (ω : ℕ → Fin 3) (t : ac_Tpl) (i0 i1 i2 i3 : ℕ) : Prop :=
  ω i0 = t.1.1 ∧ ω i1 = t.1.2.1 ∧ ω i2 = t.1.2.2.1 ∧ ω i3 = t.1.2.2.2 ∧
    ac_pdiff ω i0 i1 i2 = t.2.1 ∧ ac_pdiff ω i1 i2 i3 = t.2.2

-- Option-table membership from block data
private theorem ac_mem_opts (ch : Bool) (α' α : Fin 3) (u : List (Fin 3))
    (r : ℕ) (hr : r < 6) (hu : u ∈ ac_imgs ch α') (hget : u.getD r 0 = α) :
    (α', ac_pre u r) ∈ ac_opts ch α := by
  unfold ac_opts
  rw [List.mem_flatMap]
  refine ⟨α', by simp, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨u, hu, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨r, List.mem_range.mpr hr, ?_⟩
  change (if u.getD r 0 = α then some (α', ac_pre u r) else none) =
    some (α', ac_pre u r)
  rw [hget]
  exact ite_eq_left rfl

-- M-row expansions (M a c = count of a in hImg c)
private theorem ac_M_row0 (f : Fin 3 → ℤ) :
    ∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) * f c = 4 * f 0 + 2 * f 1 + f 2 := by
  simp only [Fin.sum_univ_three]
  have m00 : (ac_hImg 0).count 0 = 4 := ac_M_entries.1
  have m10 : (ac_hImg 1).count 0 = 2 := ac_M_entries.2.1
  have m20 : (ac_hImg 2).count 0 = 1 := ac_M_entries.2.2.1
  rw [m00, m10, m20]
  push_cast
  ring

private theorem ac_M_row1 (f : Fin 3 → ℤ) :
    ∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) * f c = f 0 + 3 * f 1 + f 2 := by
  simp only [Fin.sum_univ_three]
  have m01 : (ac_hImg 0).count 1 = 1 := ac_M_entries.2.2.2.1
  have m11 : (ac_hImg 1).count 1 = 3 := ac_M_entries.2.2.2.2.1
  have m21 : (ac_hImg 2).count 1 = 1 := ac_M_entries.2.2.2.2.2.1
  rw [m01, m11, m21]
  push_cast
  ring

private theorem ac_M_row2 (f : Fin 3 → ℤ) :
    ∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) * f c = f 0 + f 1 + 4 * f 2 := by
  simp only [Fin.sum_univ_three]
  have m02 : (ac_hImg 0).count 2 = 1 := ac_M_entries.2.2.2.2.2.2.1
  have m12 : (ac_hImg 1).count 2 = 1 := ac_M_entries.2.2.2.2.2.2.2.1
  have m22 : (ac_hImg 2).count 2 = 4 := ac_M_entries.2.2.2.2.2.2.2.2
  rw [m02, m12, m22]
  push_cast
  ring

-- N5c/N3-corollary: window formula in ℤ
private theorem ac_window_sub (ω δ : ℕ → Fin 3) (blk : ℕ → List (Fin 3))
    (M : Fin 3 → Fin 3 → ℕ)
    (hlen : ∀ q, (blk q).length = 6)
    (hω : ∀ q r, r < 6 → ω (6 * q + r) = (blk q).getD r 0)
    (hM : ∀ a q, (blk q).count a = M a (δ q))
    (a : Fin 3) (q q' r r' : ℕ) (hr : r < 6) (hr' : r' < 6)
    (hle : 6 * q + r ≤ 6 * q' + r') :
    (ac_cnt ω a (6 * q + r) (6 * q' + r') : ℤ) =
      ∑ c : Fin 3, (M a c : ℤ) * (ac_cnt δ c q q') +
        (((blk q').take r').count a : ℤ) -
        (((blk q).take r).count a : ℤ) := by
  have hq : q ≤ q' := by omega
  have hsplit := ac_cnt_split (ω := ω) (a := a) (i := 0) (j := 6 * q + r)
    (k := 6 * q' + r') (Nat.zero_le _) hle
  have hδ : ∀ c : Fin 3, ac_cnt δ c 0 q' = ac_cnt δ c 0 q + ac_cnt δ c q q' :=
    fun c => ac_cnt_split (ω := δ) (a := c) (i := 0) (j := q) (k := q')
      (Nat.zero_le _) hq
  have e1 := ac_block_full ω δ blk M hlen hω hM a q r hr
  have e2 := ac_block_full ω δ blk M hlen hω hM a q' r' hr'
  have hsum : (∑ c : Fin 3, M a c * ac_cnt δ c 0 q') =
      (∑ c : Fin 3, M a c * ac_cnt δ c 0 q) +
        ∑ c : Fin 3, M a c * ac_cnt δ c q q' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hδ c, mul_add]
  have hX : (ac_cnt ω a (6 * q + r) (6 * q' + r') : ℤ) =
      (ac_cnt ω a 0 (6 * q' + r') : ℤ) - (ac_cnt ω a 0 (6 * q + r) : ℤ) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hsplit
    push_cast at h
    omega
  rw [hX, e1, e2, hsum]
  push_cast
  ring

-- Generic template desubstitution step.
private theorem ac_descent (ω δ' : ℕ → Fin 3) (blk : ℕ → List (Fin 3))
    (ch : Bool)
    (hlen : ∀ q, (blk q).length = 6)
    (hω : ∀ q r, r < 6 → ω (6 * q + r) = (blk q).getD r 0)
    (hmem : ∀ q, blk q ∈ ac_imgs ch (δ' q))
    (hM : ∀ a q, (blk q).count a = (ac_hImg (δ' q)).count a)
    (t : ac_Tpl) (i0 i1 i2 i3 : ℕ)
    (h01 : i0 ≤ i1) (h12 : i1 ≤ i2) (h23 : i2 ≤ i3)
    (hr : ac_realizes ω t i0 i1 i2 i3) (hspan : 6 ≤ i3 - i0) :
    ∃ p : ac_Tpl,
      ac_realizes δ' p (i0 / 6) (i1 / 6) (i2 / 6) (i3 / 6) ∧
      1 ≤ i3 / 6 - i0 / 6 ∧
      i3 / 6 - i0 / 6 < i3 - i0 ∧
      (δ' (i0 / 6), ac_pre (blk (i0 / 6)) (i0 % 6)) ∈ ac_opts ch t.1.1 ∧
      (δ' (i1 / 6), ac_pre (blk (i1 / 6)) (i1 % 6)) ∈ ac_opts ch t.1.2.1 ∧
      (δ' (i2 / 6), ac_pre (blk (i2 / 6)) (i2 % 6)) ∈ ac_opts ch t.1.2.2.1 ∧
      (δ' (i3 / 6), ac_pre (blk (i3 / 6)) (i3 % 6)) ∈ ac_opts ch t.1.2.2.2 ∧
      ac_parent t ((δ' (i0 / 6), ac_pre (blk (i0 / 6)) (i0 % 6)),
        (δ' (i1 / 6), ac_pre (blk (i1 / 6)) (i1 % 6)),
        (δ' (i2 / 6), ac_pre (blk (i2 / 6)) (i2 % 6)),
        (δ' (i3 / 6), ac_pre (blk (i3 / 6)) (i3 % 6))) = some p := by
  have hi0 : i0 = 6 * (i0 / 6) + i0 % 6 := (Nat.div_add_mod i0 6).symm
  have hi1 : i1 = 6 * (i1 / 6) + i1 % 6 := (Nat.div_add_mod i1 6).symm
  have hi2 : i2 = 6 * (i2 / 6) + i2 % 6 := (Nat.div_add_mod i2 6).symm
  have hi3 : i3 = 6 * (i3 / 6) + i3 % 6 := (Nat.div_add_mod i3 6).symm
  have hr0 : i0 % 6 < 6 := Nat.mod_lt _ (by decide)
  have hr1 : i1 % 6 < 6 := Nat.mod_lt _ (by decide)
  have hr2 : i2 % 6 < 6 := Nat.mod_lt _ (by decide)
  have hr3 : i3 % 6 < 6 := Nat.mod_lt _ (by decide)
  obtain ⟨g0, g1, g2, g3, pd1, pd2⟩ := hr
  obtain ⟨hSpos, hSlt⟩ := ac_span_descent hspan
  have o0 : (δ' (i0 / 6), ac_pre (blk (i0 / 6)) (i0 % 6)) ∈ ac_opts ch t.1.1 := by
    apply ac_mem_opts _ _ _ _ _ hr0 (hmem _) _
    have e : ω (6 * (i0 / 6) + i0 % 6) = t.1.1 := by rw [← hi0]; exact g0
    rw [hω _ _ hr0] at e
    exact e
  have o1 : (δ' (i1 / 6), ac_pre (blk (i1 / 6)) (i1 % 6)) ∈ ac_opts ch t.1.2.1 := by
    apply ac_mem_opts _ _ _ _ _ hr1 (hmem _) _
    have e : ω (6 * (i1 / 6) + i1 % 6) = t.1.2.1 := by rw [← hi1]; exact g1
    rw [hω _ _ hr1] at e
    exact e
  have o2 : (δ' (i2 / 6), ac_pre (blk (i2 / 6)) (i2 % 6)) ∈ ac_opts ch t.1.2.2.1 := by
    apply ac_mem_opts _ _ _ _ _ hr2 (hmem _) _
    have e : ω (6 * (i2 / 6) + i2 % 6) = t.1.2.2.1 := by rw [← hi2]; exact g2
    rw [hω _ _ hr2] at e
    exact e
  have o3 : (δ' (i3 / 6), ac_pre (blk (i3 / 6)) (i3 % 6)) ∈ ac_opts ch t.1.2.2.2 := by
    apply ac_mem_opts _ _ _ _ _ hr3 (hmem _) _
    have e : ω (6 * (i3 / 6) + i3 % 6) = t.1.2.2.2 := by rw [← hi3]; exact g3
    rw [hω _ _ hr3] at e
    exact e
  have le01 : 6 * (i0 / 6) + i0 % 6 ≤ 6 * (i1 / 6) + i1 % 6 := by
    rw [← hi0, ← hi1]; exact h01
  have le12 : 6 * (i1 / 6) + i1 % 6 ≤ 6 * (i2 / 6) + i2 % 6 := by
    rw [← hi1, ← hi2]; exact h12
  have le23 : 6 * (i2 / 6) + i2 % 6 ≤ 6 * (i3 / 6) + i3 % 6 := by
    rw [← hi2, ← hi3]; exact h23
  have W01_0 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 0 (i0 / 6) (i1 / 6) (i0 % 6) (i1 % 6) hr0 hr1 le01
  have W01_1 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 1 (i0 / 6) (i1 / 6) (i0 % 6) (i1 % 6) hr0 hr1 le01
  have W01_2 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 2 (i0 / 6) (i1 / 6) (i0 % 6) (i1 % 6) hr0 hr1 le01
  have W12_0 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 0 (i1 / 6) (i2 / 6) (i1 % 6) (i2 % 6) hr1 hr2 le12
  have W12_1 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 1 (i1 / 6) (i2 / 6) (i1 % 6) (i2 % 6) hr1 hr2 le12
  have W12_2 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 2 (i1 / 6) (i2 / 6) (i1 % 6) (i2 % 6) hr1 hr2 le12
  have W23_0 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 0 (i2 / 6) (i3 / 6) (i2 % 6) (i3 % 6) hr2 hr3 le23
  have W23_1 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 1 (i2 / 6) (i3 / 6) (i2 % 6) (i3 % 6) hr2 hr3 le23
  have W23_2 := ac_window_sub ω δ' blk (fun a c => (ac_hImg c).count a)
    hlen hω hM 2 (i2 / 6) (i3 / 6) (i2 % 6) (i3 % 6) hr2 hr3 le23
  have e1_0 : (ac_cnt ω 0 i1 i2 : ℤ) - (ac_cnt ω 0 i0 i1 : ℤ) = t.2.1.1 := by
    have h := congrArg (fun v : ℤ × ℤ × ℤ => v.1) pd1
    simpa [ac_pdiff] using h
  have e1_1 : (ac_cnt ω 1 i1 i2 : ℤ) - (ac_cnt ω 1 i0 i1 : ℤ) = t.2.1.2.1 := by
    have h := congrArg (fun v : ℤ × ℤ × ℤ => v.2.1) pd1
    simpa [ac_pdiff] using h
  have e1_2 : (ac_cnt ω 2 i1 i2 : ℤ) - (ac_cnt ω 2 i0 i1 : ℤ) = t.2.1.2.2 := by
    have h := congrArg (fun v : ℤ × ℤ × ℤ => v.2.2) pd1
    simpa [ac_pdiff] using h
  have e2_0 : (ac_cnt ω 0 i2 i3 : ℤ) - (ac_cnt ω 0 i1 i2 : ℤ) = t.2.2.1 := by
    have h := congrArg (fun v : ℤ × ℤ × ℤ => v.1) pd2
    simpa [ac_pdiff] using h
  have e2_1 : (ac_cnt ω 1 i2 i3 : ℤ) - (ac_cnt ω 1 i1 i2 : ℤ) = t.2.2.2.1 := by
    have h := congrArg (fun v : ℤ × ℤ × ℤ => v.2.1) pd2
    simpa [ac_pdiff] using h
  have e2_2 : (ac_cnt ω 2 i2 i3 : ℤ) - (ac_cnt ω 2 i1 i2 : ℤ) = t.2.2.2.2 := by
    have h := congrArg (fun v : ℤ × ℤ × ℤ => v.2.2) pd2
    simpa [ac_pdiff] using h
  rw [hi0, hi1, hi2] at e1_0 e1_1 e1_2
  rw [hi1, hi2, hi3] at e2_0 e2_1 e2_2
  have be0_0 : (ac_pre (blk (i0 / 6)) (i0 % 6)).1 =
      (((blk (i0 / 6)).take (i0 % 6)).count 0 : ℤ) := rfl
  have be1_0 : (ac_pre (blk (i1 / 6)) (i1 % 6)).1 =
      (((blk (i1 / 6)).take (i1 % 6)).count 0 : ℤ) := rfl
  have be2_0 : (ac_pre (blk (i2 / 6)) (i2 % 6)).1 =
      (((blk (i2 / 6)).take (i2 % 6)).count 0 : ℤ) := rfl
  have be3_0 : (ac_pre (blk (i3 / 6)) (i3 % 6)).1 =
      (((blk (i3 / 6)).take (i3 % 6)).count 0 : ℤ) := rfl
  have be0_1 : (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1 =
      (((blk (i0 / 6)).take (i0 % 6)).count 1 : ℤ) := rfl
  have be1_1 : (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1 =
      (((blk (i1 / 6)).take (i1 % 6)).count 1 : ℤ) := rfl
  have be2_1 : (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 =
      (((blk (i2 / 6)).take (i2 % 6)).count 1 : ℤ) := rfl
  have be3_1 : (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1 =
      (((blk (i3 / 6)).take (i3 % 6)).count 1 : ℤ) := rfl
  have be0_2 : (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2 =
      (((blk (i0 / 6)).take (i0 % 6)).count 2 : ℤ) := rfl
  have be1_2 : (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2 =
      (((blk (i1 / 6)).take (i1 % 6)).count 2 : ℤ) := rfl
  have be2_2 : (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2 =
      (((blk (i2 / 6)).take (i2 % 6)).count 2 : ℤ) := rfl
  have be3_2 : (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2 =
      (((blk (i3 / 6)).take (i3 % 6)).count 2 : ℤ) := rfl
  have bd1_0 : (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).1 =
      (ac_cnt δ' 0 (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' 0 (i0 / 6) (i1 / 6) : ℤ) :=
    rfl
  have bd1_1 : (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.1 =
      (ac_cnt δ' 1 (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' 1 (i0 / 6) (i1 / 6) : ℤ) :=
    rfl
  have bd1_2 : (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.2 =
      (ac_cnt δ' 2 (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' 2 (i0 / 6) (i1 / 6) : ℤ) :=
    rfl
  have bd2_0 : (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).1 =
      (ac_cnt δ' 0 (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' 0 (i1 / 6) (i2 / 6) : ℤ) :=
    rfl
  have bd2_1 : (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.1 =
      (ac_cnt δ' 1 (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' 1 (i1 / 6) (i2 / 6) : ℤ) :=
    rfl
  have bd2_2 : (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.2 =
      (ac_cnt δ' 2 (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' 2 (i1 / 6) (i2 / 6) : ℤ) :=
    rfl
  have key10 : 4 * (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).1 +
        2 * (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.1 +
        (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.2
      = t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).1 := by
    have ssub : (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
          ((ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)))
        = (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
            (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ))
          - (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
            (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    have hSig : (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
          ((ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)))
        = t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
          + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1
          - (ac_pre (blk (i2 / 6)) (i2 % 6)).1 := by
      rw [ssub]
      linear_combination -W12_0 + W01_0 + e1_0 + be0_0 - 2 * be1_0 + be2_0
    simp only [ac_M_row0] at hSig
    rw [← bd1_0, ← bd1_1, ← bd1_2] at hSig
    exact hSig
  have key11 : (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).1 +
        3 * (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.1 +
        (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.2
      = t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 := by
    have ssub : (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
          ((ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)))
        = (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
            (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ))
          - (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
            (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    have hSig : (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
          ((ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)))
        = t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
          + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
          - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 := by
      rw [ssub]
      linear_combination -W12_1 + W01_1 + e1_1 + be0_1 - 2 * be1_1 + be2_1
    simp only [ac_M_row1] at hSig
    rw [← bd1_0, ← bd1_1, ← bd1_2] at hSig
    exact hSig
  have key12 : (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).1 +
        (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.1 +
        4 * (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.2
      = t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2 := by
    have ssub : (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
          ((ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)))
        = (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
            (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ))
          - (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
            (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    have hSig : (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
          ((ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ) - (ac_cnt δ' c (i0 / 6) (i1 / 6) : ℤ)))
        = t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
          + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
          - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2 := by
      rw [ssub]
      linear_combination -W12_2 + W01_2 + e1_2 + be0_2 - 2 * be1_2 + be2_2
    simp only [ac_M_row2] at hSig
    rw [← bd1_0, ← bd1_1, ← bd1_2] at hSig
    exact hSig
  have key20 : 4 * (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).1 +
        2 * (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.1 +
        (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.2
      = t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).1 := by
    have ssub : (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
          ((ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)))
        = (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
            (ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ))
          - (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
            (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    have hSig : (∑ c : Fin 3, ((ac_hImg c).count 0 : ℤ) *
          ((ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)))
        = t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
          + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1
          - (ac_pre (blk (i3 / 6)) (i3 % 6)).1 := by
      rw [ssub]
      linear_combination -W23_0 + W12_0 + e2_0 + be1_0 - 2 * be2_0 + be3_0
    simp only [ac_M_row0] at hSig
    rw [← bd2_0, ← bd2_1, ← bd2_2] at hSig
    exact hSig
  have key21 : (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).1 +
        3 * (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.1 +
        (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.2
      = t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1 := by
    have ssub : (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
          ((ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)))
        = (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
            (ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ))
          - (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
            (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    have hSig : (∑ c : Fin 3, ((ac_hImg c).count 1 : ℤ) *
          ((ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)))
        = t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
          + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1
          - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1 := by
      rw [ssub]
      linear_combination -W23_1 + W12_1 + e2_1 + be1_1 - 2 * be2_1 + be3_1
    simp only [ac_M_row1] at hSig
    rw [← bd2_0, ← bd2_1, ← bd2_2] at hSig
    exact hSig
  have key22 : (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).1 +
        (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.1 +
        4 * (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.2
      = t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2 := by
    have ssub : (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
          ((ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)))
        = (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
            (ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ))
          - (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
            (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    have hSig : (∑ c : Fin 3, ((ac_hImg c).count 2 : ℤ) *
          ((ac_cnt δ' c (i2 / 6) (i3 / 6) : ℤ) - (ac_cnt δ' c (i1 / 6) (i2 / 6) : ℤ)))
        = t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
          + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
          - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2 := by
      rw [ssub]
      linear_combination -W23_2 + W12_2 + e2_2 + be1_2 - 2 * be2_2 + be3_2
    simp only [ac_M_row2] at hSig
    rw [← bd2_0, ← bd2_1, ← bd2_2] at hSig
    exact hSig
  obtain ⟨n1a, n1b, n1c⟩ := ac_adj_mul key10 key11 key12
  obtain ⟨n2a, n2b, n2c⟩ := ac_adj_mul key20 key21 key22
  have hdiv : (11 * (t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).1)
      - 7 * (t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1)
      - (t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2)) % 36 = 0
      ∧ (-3 * (t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).1)
      + 15 * (t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1)
      - 3 * (t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2)) % 36 = 0
      ∧ (-2 * (t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).1)
      - 2 * (t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1)
      + 10 * (t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2)) % 36 = 0
      ∧ (11 * (t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).1)
      - 7 * (t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1)
      - (t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2)) % 36 = 0
      ∧ (-3 * (t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).1)
      + 15 * (t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1)
      - 3 * (t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2)) % 36 = 0
      ∧ (-2 * (t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).1)
      - 2 * (t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1)
      + 10 * (t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2)) % 36 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hq : (11 * (t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).1)
      - 7 * (t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1)
      - (t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2)) / 36
        = (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).1
      ∧ (-3 * (t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).1)
      + 15 * (t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1)
      - 3 * (t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2)) / 36
        = (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.1
      ∧ (-2 * (t.2.1.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).1)
      - 2 * (t.2.1.2.1 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.1
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1 - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1)
      + 10 * (t.2.1.2.2 - (ac_pre (blk (i0 / 6)) (i0 % 6)).2.2
        + 2 * (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        - (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2)) / 36
        = (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6)).2.2
      ∧ (11 * (t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).1)
      - 7 * (t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1)
      - (t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2)) / 36
        = (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).1
      ∧ (-3 * (t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).1)
      + 15 * (t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1)
      - 3 * (t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2)) / 36
        = (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.1
      ∧ (-2 * (t.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).1)
      - 2 * (t.2.2.2.1 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.1
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.1 - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.1)
      + 10 * (t.2.2.2.2 - (ac_pre (blk (i1 / 6)) (i1 % 6)).2.2
        + 2 * (ac_pre (blk (i2 / 6)) (i2 % 6)).2.2
        - (ac_pre (blk (i3 / 6)) (i3 % 6)).2.2)) / 36
        = (ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6)).2.2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  refine ⟨((δ' (i0 / 6), δ' (i1 / 6), δ' (i2 / 6), δ' (i3 / 6)),
      (ac_pdiff δ' (i0 / 6) (i1 / 6) (i2 / 6),
        ac_pdiff δ' (i1 / 6) (i2 / 6) (i3 / 6))),
    ?_, hSpos, hSlt, o0, o1, o2, o3, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [ac_parent, ac_adjMul, hdiv, hq, true_and, ite_true, Prod.mk.eta]

-- Divisibility extracted from a successful parent computation.
private theorem ac_parent_div_of_some (t : ac_Tpl)
    (o0 o1 o2 o3 : Fin 3 × (ℤ × ℤ × ℤ)) (p : ac_Tpl)
    (hp : ac_parent t (o0, o1, o2, o3) = some p) :
    (11 * (t.2.1.1 - o0.2.1 + 2 * o1.2.1 - o2.2.1)
      - 7 * (t.2.1.2.1 - o0.2.2.1 + 2 * o1.2.2.1 - o2.2.2.1)
      - (t.2.1.2.2 - o0.2.2.2 + 2 * o1.2.2.2 - o2.2.2.2)) % 36 = 0 ∧
    (-3 * (t.2.1.1 - o0.2.1 + 2 * o1.2.1 - o2.2.1)
      + 15 * (t.2.1.2.1 - o0.2.2.1 + 2 * o1.2.2.1 - o2.2.2.1)
      - 3 * (t.2.1.2.2 - o0.2.2.2 + 2 * o1.2.2.2 - o2.2.2.2)) % 36 = 0 ∧
    (-2 * (t.2.1.1 - o0.2.1 + 2 * o1.2.1 - o2.2.1)
      - 2 * (t.2.1.2.1 - o0.2.2.1 + 2 * o1.2.2.1 - o2.2.2.1)
      + 10 * (t.2.1.2.2 - o0.2.2.2 + 2 * o1.2.2.2 - o2.2.2.2)) % 36 = 0 ∧
    (11 * (t.2.2.1 - o1.2.1 + 2 * o2.2.1 - o3.2.1)
      - 7 * (t.2.2.2.1 - o1.2.2.1 + 2 * o2.2.2.1 - o3.2.2.1)
      - (t.2.2.2.2 - o1.2.2.2 + 2 * o2.2.2.2 - o3.2.2.2)) % 36 = 0 ∧
    (-3 * (t.2.2.1 - o1.2.1 + 2 * o2.2.1 - o3.2.1)
      + 15 * (t.2.2.2.1 - o1.2.2.1 + 2 * o2.2.2.1 - o3.2.2.1)
      - 3 * (t.2.2.2.2 - o1.2.2.2 + 2 * o2.2.2.2 - o3.2.2.2)) % 36 = 0 ∧
    (-2 * (t.2.2.1 - o1.2.1 + 2 * o2.2.1 - o3.2.1)
      - 2 * (t.2.2.2.1 - o1.2.2.1 + 2 * o2.2.2.1 - o3.2.2.1)
      + 10 * (t.2.2.2.2 - o1.2.2.2 + 2 * o2.2.2.2 - o3.2.2.2)) % 36 = 0 := by
  by_contra hc
  have h := hp
  simp only [ac_parent, ac_adjMul, hc, ite_false] at h
  simp at h

private theorem ac_closed_spec (t : ac_Tpl) (ht : ac_T.contains t = true)
    {a0 a1 a2 a3 : Fin 3 × (ℤ × ℤ × ℤ)}
    (m0 : a0 ∈ ac_opts false t.1.1) (m1 : a1 ∈ ac_opts false t.1.2.1)
    (m2 : a2 ∈ ac_opts false t.1.2.2.1) (m3 : a3 ∈ ac_opts false t.1.2.2.2)
    (p : ac_Tpl) (hp : ac_parent t (a0, a1, a2, a3) = some p) :
    ac_T.contains p = true := by
  have hchk := ac_closedCheck_ok
  unfold ac_closedCheck at hchk
  rw [List.all_eq_true] at hchk
  have hmem : t ∈ ac_T := List.mem_of_elem_eq_true ht
  have hx := hchk t hmem
  simp only [] at hx
  rw [List.all_eq_true] at hx
  have hx0 := hx a0 m0
  rw [List.all_eq_true] at hx0
  have hx1 := hx0 a1 m1
  rw [List.all_eq_true] at hx1
  have hx2 := hx1 a2 m2
  obtain ⟨d1, d2, d3, -, -, -⟩ := ac_parent_div_of_some t a0 a1 a2 a3 p hp
  simp only [ac_adjMul, d1, d2, d3, true_and, ite_true] at hx2
  rw [List.all_eq_true] at hx2
  have hx3 := hx2 a3 m3
  simpa [hp] using hx3

private theorem ac_zero_mem (α0 α1 α2 α3 : Fin 3) :
    ((α0, α1, α2, α3), ((0, 0, 0), (0, 0, 0))) ∈ ac_zeroTemplates := by
  unfold ac_zeroTemplates
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨α0, by simp, α1, by simp, α2, by simp, α3, by simp, rfl⟩

private theorem ac_zero_spec (α0 α1 α2 α3 : Fin 3)
    {a0 a1 a2 a3 : Fin 3 × (ℤ × ℤ × ℤ)}
    (m0 : a0 ∈ ac_opts true α0) (m1 : a1 ∈ ac_opts true α1)
    (m2 : a2 ∈ ac_opts true α2) (m3 : a3 ∈ ac_opts true α3)
    (p : ac_Tpl)
    (hp : ac_parent ((α0, α1, α2, α3), ((0, 0, 0), (0, 0, 0))) (a0, a1, a2, a3) =
      some p) :
    ac_T.contains p = true := by
  have hchk := ac_zeroCheck_ok
  unfold ac_zeroCheck at hchk
  rw [List.all_eq_true] at hchk
  have hmem := ac_zero_mem α0 α1 α2 α3
  have hx := hchk _ hmem
  simp only [] at hx
  rw [List.all_eq_true] at hx
  have hx0 := hx a0 m0
  rw [List.all_eq_true] at hx0
  have hx1 := hx0 a1 m1
  rw [List.all_eq_true] at hx1
  have hx2 := hx1 a2 m2
  obtain ⟨d1, d2, d3, -, -, -⟩ := ac_parent_div_of_some _ a0 a1 a2 a3 p hp
  simp only [ac_adjMul, d1, d2, d3, true_and, ite_true] at hx2
  rw [List.all_eq_true] at hx2
  have hx3 := hx2 a3 m3
  simpa [hp] using hx3

-- Template equality from component equalities.
private theorem ac_tpl_eq (t x : ac_Tpl)
    (h0 : t.1.1 = x.1.1) (h1 : t.1.2.1 = x.1.2.1) (h2 : t.1.2.2.1 = x.1.2.2.1)
    (h3 : t.1.2.2.2 = x.1.2.2.2)
    (hd1 : t.2.1 = x.2.1) (hd2 : t.2.2 = x.2.2) : t = x :=
  Prod.ext (Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))) (Prod.ext hd1 hd2)

private theorem ac_base_spec (a b : Fin 3) (p0 p1 p2 p3 : ℕ)
    (h01 : p0 ≤ p1) (h12 : p1 ≤ p2) (h23 : p2 ≤ p3)
    (hp0 : p0 ≤ 5) (hpos : 1 ≤ p3 - p0) (hle5 : p3 - p0 ≤ 5) :
    ac_T.contains (((ac_hImg a ++ ac_hImg b).getD p0 0,
        (ac_hImg a ++ ac_hImg b).getD p1 0,
        (ac_hImg a ++ ac_hImg b).getD p2 0,
        (ac_hImg a ++ ac_hImg b).getD p3 0),
      (((ac_pu (ac_hImg a ++ ac_hImg b) p1 p2).1
          - (ac_pu (ac_hImg a ++ ac_hImg b) p0 p1).1,
        (ac_pu (ac_hImg a ++ ac_hImg b) p1 p2).2.1
          - (ac_pu (ac_hImg a ++ ac_hImg b) p0 p1).2.1,
        (ac_pu (ac_hImg a ++ ac_hImg b) p1 p2).2.2
          - (ac_pu (ac_hImg a ++ ac_hImg b) p0 p1).2.2),
       ((ac_pu (ac_hImg a ++ ac_hImg b) p2 p3).1
          - (ac_pu (ac_hImg a ++ ac_hImg b) p1 p2).1,
        (ac_pu (ac_hImg a ++ ac_hImg b) p2 p3).2.1
          - (ac_pu (ac_hImg a ++ ac_hImg b) p1 p2).2.1,
        (ac_pu (ac_hImg a ++ ac_hImg b) p2 p3).2.2
          - (ac_pu (ac_hImg a ++ ac_hImg b) p1 p2).2.2))) = false := by
  have hchk := ac_baseCheck_ok
  unfold ac_baseCheck at hchk
  rw [List.all_eq_true] at hchk
  have hp0lt : p0 < 12 := by omega
  have hp1lt : p1 < 12 := by omega
  have hp2lt : p2 < 12 := by omega
  have hp3lt : p3 < 12 := by omega
  have hx := hchk a (by simp)
  simp only [] at hx
  rw [List.all_eq_true] at hx
  have hxb := hx b (by simp)
  rw [List.all_eq_true] at hxb
  have hx0 := hxb p0 (List.mem_range.mpr hp0lt)
  rw [List.all_eq_true] at hx0
  have hx1 := hx0 p1 (List.mem_range.mpr hp1lt)
  rw [List.all_eq_true] at hx1
  have hx2 := hx1 p2 (List.mem_range.mpr hp2lt)
  rw [List.all_eq_true] at hx2
  have hx3 := hx2 p3 (List.mem_range.mpr hp3lt)
  simp only [h01, h12, h23, hp0, hpos, hle5, true_and, ite_true] at hx3
  simpa using hx3

private theorem ac_noaa_spec (a b : Fin 3) (c c' : Bool) (i : ℕ) (hi : i < 10) :
    ¬ ((ac_img c a ++ ac_img c' b).getD i 0
        = (ac_img c a ++ ac_img c' b).getD (i + 1) 0 ∧
      (ac_img c a ++ ac_img c' b).getD (i + 1) 0
        = (ac_img c a ++ ac_img c' b).getD (i + 2) 0) := by
  have hchk := ac_noaaCheck_ok
  unfold ac_noaaCheck at hchk
  rw [List.all_eq_true] at hchk
  have hx := hchk a (by simp)
  simp only [] at hx
  rw [List.all_eq_true] at hx
  have hxb := hx b (by simp)
  rw [List.all_eq_true] at hxb
  have hxc := hxb c (by cases c <;> simp)
  rw [List.all_eq_true] at hxc
  have hxc' := hxc c' (by cases c' <;> simp)
  rw [List.all_eq_true] at hxc'
  have hxi := hxc' i (List.mem_range.mpr hi)
  exact of_decide_eq_true hxi

private theorem ac_hImg_len : ∀ a : Fin 3, (ac_hImg a).length = 6 := by decide
private theorem ac_hImg_mem : ∀ a : Fin 3, ac_hImg a ∈ ac_imgs false a := by decide
private theorem ac_img_memC : ∀ (c : Bool) (a : Fin 3),
    ac_img c a ∈ ac_imgs true a := by decide

-- Base case: span in [1,5] contradicts the base checker.
private theorem ac_base_contra (t : ac_Tpl) (ht : ac_T.contains t = true)
    (i0 i1 i2 i3 : ℕ) (h01 : i0 ≤ i1) (h12 : i1 ≤ i2) (h23 : i2 ≤ i3)
    (hpos : 1 ≤ i3 - i0) (hle5 : i3 - i0 ≤ 5)
    (hr : ac_realizes ac_delta t i0 i1 i2 i3) : False := by
  set Q : ℕ := i0 / 6 with hQdef
  have h6Q0 : 6 * Q ≤ i0 := by omega
  have hi0e : i0 = 6 * Q + (i0 - 6 * Q) := (Nat.add_sub_cancel' h6Q0).symm
  have h6Q1 : 6 * Q ≤ i1 := by omega
  have hi1e : i1 = 6 * Q + (i1 - 6 * Q) := (Nat.add_sub_cancel' h6Q1).symm
  have h6Q2 : 6 * Q ≤ i2 := by omega
  have hi2e : i2 = 6 * Q + (i2 - 6 * Q) := (Nat.add_sub_cancel' h6Q2).symm
  have h6Q3 : 6 * Q ≤ i3 := by omega
  have hi3e : i3 = 6 * Q + (i3 - 6 * Q) := (Nat.add_sub_cancel' h6Q3).symm
  have hp0 : i0 - 6 * Q < 6 := by omega
  have hp1 : i1 - 6 * Q < 12 := by omega
  have hp2 : i2 - 6 * Q < 12 := by omega
  have hp3 : i3 - 6 * Q < 12 := by omega
  have hp0b : i0 - 6 * Q < 12 := by omega
  have hq01 : i0 - 6 * Q ≤ i1 - 6 * Q := by omega
  have hq12 : i1 - 6 * Q ≤ i2 - 6 * Q := by omega
  have hq23 : i2 - 6 * Q ≤ i3 - 6 * Q := by omega
  have hspan : (i3 - 6 * Q) - (i0 - 6 * Q) = i3 - i0 := by omega
  set u : List (Fin 3) :=
    ac_hImg (ac_delta Q) ++ ac_hImg (ac_delta (Q + 1)) with hudef
  have hulen : u.length = 12 := by
    rw [hudef, List.length_append, ac_hImg_len, ac_hImg_len]
  have hδu : ∀ p, p < 12 → ac_delta (6 * Q + p) = u.getD p 0 := by
    intro p hp
    have h1 : p < (ac_hImg (ac_delta Q) ++ ac_hImg (ac_delta (Q + 1))).length := by
      rw [List.length_append, ac_hImg_len, ac_hImg_len]; omega
    by_cases h6 : p < 6
    · have e1 : ac_delta (6 * Q + p) = (ac_hImg (ac_delta Q)).getD p 0 :=
        ac_delta_unfold Q p h6
      have h0 : p < (ac_hImg (ac_delta Q)).length := by
        rw [ac_hImg_len]; exact h6
      rw [e1, hudef, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h0]
      exact (List.getElem_append_left h0).symm
    · have e2 : 6 * Q + p = 6 * (Q + 1) + (p - 6) := by omega
      have hp6 : p - 6 < 6 := by omega
      have e3 : ac_delta (6 * (Q + 1) + (p - 6)) =
          (ac_hImg (ac_delta (Q + 1))).getD (p - 6) 0 :=
        ac_delta_unfold (Q + 1) (p - 6) hp6
      have h2 : p - 6 < (ac_hImg (ac_delta (Q + 1))).length := by
        rw [ac_hImg_len]; exact hp6
      rw [e2, e3, hudef, List.getD_eq_getElem _ _ h1,
        List.getD_eq_getElem _ _ h2]
      have hle : (ac_hImg (ac_delta Q)).length ≤ p := by
        rw [ac_hImg_len]; omega
      have g := List.getElem_append_right (as := ac_hImg (ac_delta Q))
        (bs := ac_hImg (ac_delta (Q + 1))) (i := p) hle (h₂ := h1)
      simp only [ac_hImg_len] at g
      exact g.symm
  have hwin : ∀ (t L : ℕ), t + L ≤ 12 → ∀ a : Fin 3,
      ac_cnt ac_delta a (6 * Q + t) (6 * Q + t + L) =
        (((u.drop t).take L).count a) := by
    intro t L htL a
    have h := ac_cnt_range ac_delta a (6 * Q + t) L
    rw [h]
    congr 1
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, List.length_take, List.length_drop,
        hulen]
      omega
    · intro m hm1 hm2
      have hmL : m < L := by simpa [List.length_map, List.length_range] using hm1
      have htm : t + m < 12 := by omega
      have hlen_m : t + m < u.length := by rw [hulen]; exact htm
      rw [List.getElem_map,
        List.getElem_range (by simpa [List.length_map] using hm1)]
      have eδ : ac_delta (6 * Q + t + m) = u.getD (t + m) 0 := by
        have e : 6 * Q + t + m = 6 * Q + (t + m) := by omega
        rw [e]
        exact hδu (t + m) htm
      rw [eδ, List.getD_eq_getElem _ _ hlen_m, List.getElem_take,
        List.getElem_drop]
  obtain ⟨g0, g1, g2, g3, pd1, pd2⟩ := hr
  have e0 : t.1.1 = u.getD (i0 - 6 * Q) 0 := by
    have h' := hδu (i0 - 6 * Q) hp0b
    rw [← hi0e] at h'
    exact g0.symm.trans h'
  have e1 : t.1.2.1 = u.getD (i1 - 6 * Q) 0 := by
    have h' := hδu (i1 - 6 * Q) hp1
    rw [← hi1e] at h'
    exact g1.symm.trans h'
  have e2 : t.1.2.2.1 = u.getD (i2 - 6 * Q) 0 := by
    have h' := hδu (i2 - 6 * Q) hp2
    rw [← hi2e] at h'
    exact g2.symm.trans h'
  have e3 : t.1.2.2.2 = u.getD (i3 - 6 * Q) 0 := by
    have h' := hδu (i3 - 6 * Q) hp3
    rw [← hi3e] at h'
    exact g3.symm.trans h'
  have w01 : ∀ a : Fin 3, ac_cnt ac_delta a i0 i1 =
      (((u.drop (i0 - 6 * Q)).take ((i1 - 6 * Q) - (i0 - 6 * Q))).count a) := by
    intro a
    have h' := hwin (i0 - 6 * Q) ((i1 - 6 * Q) - (i0 - 6 * Q)) (by omega) a
    rw [← hi0e] at h'
    have hi01 : i0 + ((i1 - 6 * Q) - (i0 - 6 * Q)) = i1 := by omega
    rw [hi01] at h'
    exact h'
  have w12 : ∀ a : Fin 3, ac_cnt ac_delta a i1 i2 =
      (((u.drop (i1 - 6 * Q)).take ((i2 - 6 * Q) - (i1 - 6 * Q))).count a) := by
    intro a
    have h' := hwin (i1 - 6 * Q) ((i2 - 6 * Q) - (i1 - 6 * Q)) (by omega) a
    rw [← hi1e] at h'
    have hi12 : i1 + ((i2 - 6 * Q) - (i1 - 6 * Q)) = i2 := by omega
    rw [hi12] at h'
    exact h'
  have w23 : ∀ a : Fin 3, ac_cnt ac_delta a i2 i3 =
      (((u.drop (i2 - 6 * Q)).take ((i3 - 6 * Q) - (i2 - 6 * Q))).count a) := by
    intro a
    have h' := hwin (i2 - 6 * Q) ((i3 - 6 * Q) - (i2 - 6 * Q)) (by omega) a
    rw [← hi2e] at h'
    have hi23 : i2 + ((i3 - 6 * Q) - (i2 - 6 * Q)) = i3 := by omega
    rw [hi23] at h'
    exact h'
  have hd1 : t.2.1 = ((ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).1,
      (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.1,
      (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.2) := by
    have c0 : (ac_cnt ac_delta 0 i1 i2 : ℤ) - (ac_cnt ac_delta 0 i0 i1 : ℤ) =
        (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1
          - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).1 := by
      have q1 : (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1 =
          (((u.drop (i1 - 6 * Q)).take ((i2 - 6 * Q) - (i1 - 6 * Q))).count 0 :
            ℤ) := rfl
      have q0 : (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).1 =
          (((u.drop (i0 - 6 * Q)).take ((i1 - 6 * Q) - (i0 - 6 * Q))).count 0 :
            ℤ) := rfl
      rw [q1, q0, ← w12 0, ← w01 0]
    have c1 : (ac_cnt ac_delta 1 i1 i2 : ℤ) - (ac_cnt ac_delta 1 i0 i1 : ℤ) =
        (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1
          - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.1 := by
      have q1 : (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1 =
          (((u.drop (i1 - 6 * Q)).take ((i2 - 6 * Q) - (i1 - 6 * Q))).count 1 :
            ℤ) := rfl
      have q0 : (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.1 =
          (((u.drop (i0 - 6 * Q)).take ((i1 - 6 * Q) - (i0 - 6 * Q))).count 1 :
            ℤ) := rfl
      rw [q1, q0, ← w12 1, ← w01 1]
    have c2 : (ac_cnt ac_delta 2 i1 i2 : ℤ) - (ac_cnt ac_delta 2 i0 i1 : ℤ) =
        (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2
          - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.2 := by
      have q1 : (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2 =
          (((u.drop (i1 - 6 * Q)).take ((i2 - 6 * Q) - (i1 - 6 * Q))).count 2 :
            ℤ) := rfl
      have q0 : (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.2 =
          (((u.drop (i0 - 6 * Q)).take ((i1 - 6 * Q) - (i0 - 6 * Q))).count 2 :
            ℤ) := rfl
      rw [q1, q0, ← w12 2, ← w01 2]
    have hpd : ac_pdiff ac_delta i0 i1 i2 = ((ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).1,
      (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.1,
      (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.2) :=
      Prod.ext c0 (Prod.ext c1 c2)
    exact pd1.symm.trans hpd
  have hd2 : t.2.2 = ((ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).1
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1,
      (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.1
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1,
      (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.2
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2) := by
    have c0 : (ac_cnt ac_delta 0 i2 i3 : ℤ) - (ac_cnt ac_delta 0 i1 i2 : ℤ) =
        (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).1
          - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1 := by
      have q1 : (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).1 =
          (((u.drop (i2 - 6 * Q)).take ((i3 - 6 * Q) - (i2 - 6 * Q))).count 0 :
            ℤ) := rfl
      have q0 : (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1 =
          (((u.drop (i1 - 6 * Q)).take ((i2 - 6 * Q) - (i1 - 6 * Q))).count 0 :
            ℤ) := rfl
      rw [q1, q0, ← w23 0, ← w12 0]
    have c1 : (ac_cnt ac_delta 1 i2 i3 : ℤ) - (ac_cnt ac_delta 1 i1 i2 : ℤ) =
        (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.1
          - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1 := by
      have q1 : (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.1 =
          (((u.drop (i2 - 6 * Q)).take ((i3 - 6 * Q) - (i2 - 6 * Q))).count 1 :
            ℤ) := rfl
      have q0 : (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1 =
          (((u.drop (i1 - 6 * Q)).take ((i2 - 6 * Q) - (i1 - 6 * Q))).count 1 :
            ℤ) := rfl
      rw [q1, q0, ← w23 1, ← w12 1]
    have c2 : (ac_cnt ac_delta 2 i2 i3 : ℤ) - (ac_cnt ac_delta 2 i1 i2 : ℤ) =
        (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.2
          - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2 := by
      have q1 : (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.2 =
          (((u.drop (i2 - 6 * Q)).take ((i3 - 6 * Q) - (i2 - 6 * Q))).count 2 :
            ℤ) := rfl
      have q0 : (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2 =
          (((u.drop (i1 - 6 * Q)).take ((i2 - 6 * Q) - (i1 - 6 * Q))).count 2 :
            ℤ) := rfl
      rw [q1, q0, ← w23 2, ← w12 2]
    have hpd : ac_pdiff ac_delta i1 i2 i3 = ((ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).1
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1,
      (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.1
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1,
      (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.2
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2) :=
      Prod.ext c0 (Prod.ext c1 c2)
    exact pd2.symm.trans hpd
  have teq : t = ((u.getD (i0 - 6 * Q) 0, u.getD (i1 - 6 * Q) 0,
      u.getD (i2 - 6 * Q) 0, u.getD (i3 - 6 * Q) 0),
    (((ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).1,
      (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.1,
      (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2
        - (ac_pu u (i0 - 6 * Q) (i1 - 6 * Q)).2.2),
     ((ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).1
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).1,
      (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.1
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.1,
      (ac_pu u (i2 - 6 * Q) (i3 - 6 * Q)).2.2
        - (ac_pu u (i1 - 6 * Q) (i2 - 6 * Q)).2.2))) :=
    ac_tpl_eq t _ e0 e1 e2 e3 hd1 hd2
  have hfalse := ac_base_spec (ac_delta Q) (ac_delta (Q + 1)) (i0 - 6 * Q)
    (i1 - 6 * Q) (i2 - 6 * Q) (i3 - 6 * Q) hq01 hq12 hq23 (by omega)
    (by omega) (by omega)
  rw [teq, hudef] at ht
  rw [hfalse] at ht
  simp at ht

-- No member of T is realized in δ with positive span.
private theorem ac_delta_no_T_aux : ∀ S : ℕ, ∀ (t : ac_Tpl),
    ac_T.contains t = true → ∀ i0 i1 i2 i3 : ℕ, i0 ≤ i1 → i1 ≤ i2 → i2 ≤ i3 →
    i3 - i0 = S → 1 ≤ S → ¬ ac_realizes ac_delta t i0 i1 i2 i3 := by
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro t ht i0 i1 i2 i3 h01 h12 h23 hSeq hpos hr
    by_cases hsmall : S ≤ 5
    · subst hSeq
      exact ac_base_contra t ht i0 i1 i2 i3 h01 h12 h23 hpos hsmall hr
    · have hspan : 6 ≤ i3 - i0 := by omega
      obtain ⟨p, hreal, hpos', hlt, m0, m1, m2, m3, hpar⟩ :=
        ac_descent ac_delta ac_delta (fun q => ac_hImg (ac_delta q)) false
          (fun q => ac_hImg_len _) (fun q r hr => ac_delta_unfold q r hr)
          (fun q => ac_hImg_mem _) (fun a q => rfl)
          t i0 i1 i2 i3 h01 h12 h23 hr hspan
      have hpmem : ac_T.contains p = true :=
        ac_closed_spec t ht m0 m1 m2 m3 p hpar
      have hq01 : i0 / 6 ≤ i1 / 6 := ac_div_mono h01
      have hq12 : i1 / 6 ≤ i2 / 6 := ac_div_mono h12
      have hq23 : i2 / 6 ≤ i3 / 6 := ac_div_mono h23
      have hltS : i3 / 6 - i0 / 6 < S := by omega
      exact ih (i3 / 6 - i0 / 6) hltS p hpmem (i0 / 6) (i1 / 6) (i2 / 6)
        (i3 / 6) hq01 hq12 hq23 rfl hpos' hreal

private theorem ac_delta_no_T (t : ac_Tpl) (ht : ac_T.contains t = true)
    (i0 i1 i2 i3 : ℕ) (h01 : i0 ≤ i1) (h12 : i1 ≤ i2) (h23 : i2 ≤ i3)
    (hpos : 1 ≤ i3 - i0) : ¬ ac_realizes ac_delta t i0 i1 i2 i3 :=
  ac_delta_no_T_aux (i3 - i0) t ht i0 i1 i2 i3 h01 h12 h23 rfl hpos

-- Every choice word is abelian-cube-free.
private theorem ac_omega_cubeFree (b : ℕ → Bool) (i ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ¬ (∀ a : Fin 3, ac_cnt (ac_omega b) a i (i + ℓ) =
        ac_cnt (ac_omega b) a (i + ℓ) (i + 2 * ℓ) ∧
      ac_cnt (ac_omega b) a (i + ℓ) (i + 2 * ℓ) =
        ac_cnt (ac_omega b) a (i + 2 * ℓ) (i + 3 * ℓ)) := by
  intro hcube
  by_cases h1 : ℓ = 1
  · subst h1
    have e2 : i + 2 * 1 = i + 1 + 1 := by omega
    have e3 : i + 3 * 1 = i + 1 + 1 + 1 := by omega
    rw [e2, e3] at hcube
    have ind : ∀ (k : ℕ) (a : Fin 3), ac_cnt (ac_omega b) a k (k + 1) =
        (if ac_omega b k = a then 1 else 0) := by
      intro k a
      unfold ac_cnt
      have hsing : Finset.Ico k (k + 1) = {k} := by
        ext j
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        constructor
        · intro hj; obtain ⟨hj1, hj2⟩ := hj; omega
        · intro hj; subst hj; exact ⟨le_refl _, Nat.lt_succ_self _⟩
      rw [hsing, Finset.filter_singleton]
      by_cases h : ac_omega b k = a <;> simp [h]
    have h01 : ac_omega b (i + 1) = ac_omega b i := by
      have h := (hcube (ac_omega b i)).1
      rw [ind, ind] at h
      by_cases hc : ac_omega b (i + 1) = ac_omega b i
      · exact hc
      · rw [ite_eq_right hc] at h
        simp at h
    have h12 : ac_omega b (i + 1 + 1) = ac_omega b (i + 1) := by
      have h := (hcube (ac_omega b (i + 1))).2
      rw [ind, ind] at h
      by_cases hc : ac_omega b (i + 1 + 1) = ac_omega b (i + 1)
      · exact hc
      · rw [ite_eq_right hc] at h
        simp at h
    set Q : ℕ := i / 6 with hQdef
    have h6Q : 6 * Q ≤ i := by omega
    have hie : i = 6 * Q + (i - 6 * Q) := (Nat.add_sub_cancel' h6Q).symm
    have hp10 : i - 6 * Q < 10 := by omega
    have hωu : ∀ p, p < 12 →
        ac_omega b (6 * Q + p) =
          (ac_img (b Q) (ac_delta Q) ++
            ac_img (b (Q + 1)) (ac_delta (Q + 1))).getD p 0 := by
      intro p hp12
      have h1 : p < (ac_img (b Q) (ac_delta Q) ++
          ac_img (b (Q + 1)) (ac_delta (Q + 1))).length := by
        rw [List.length_append, ac_img_length, ac_img_length]; omega
      by_cases h6 : p < 6
      · have e1 : ac_omega b (6 * Q + p) =
            (ac_img (b Q) (ac_delta Q)).getD p 0 :=
          ac_omega_unfold b Q p h6
        have h0 : p < (ac_img (b Q) (ac_delta Q)).length := by
          rw [ac_img_length]; exact h6
        rw [e1, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h0]
        exact (List.getElem_append_left h0).symm
      · have e2 : 6 * Q + p = 6 * (Q + 1) + (p - 6) := by omega
        have hp6 : p - 6 < 6 := by omega
        have e3 : ac_omega b (6 * (Q + 1) + (p - 6)) =
            (ac_img (b (Q + 1)) (ac_delta (Q + 1))).getD (p - 6) 0 :=
          ac_omega_unfold b (Q + 1) (p - 6) hp6
        have h2 : p - 6 < (ac_img (b (Q + 1)) (ac_delta (Q + 1))).length := by
          rw [ac_img_length]; exact hp6
        rw [e2, e3, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
        have hle : (ac_img (b Q) (ac_delta Q)).length ≤ p := by
          rw [ac_img_length]; omega
        have g := List.getElem_append_right (as := ac_img (b Q) (ac_delta Q))
          (bs := ac_img (b (Q + 1)) (ac_delta (Q + 1))) (i := p) hle (h₂ := h1)
        simp only [ac_img_length] at g
        exact g.symm
    have g0 : ac_omega b i =
        (ac_img (b Q) (ac_delta Q) ++
          ac_img (b (Q + 1)) (ac_delta (Q + 1))).getD (i - 6 * Q) 0 := by
      have h' := hωu (i - 6 * Q) (by omega)
      rwa [← hie] at h'
    have g1 : ac_omega b (i + 1) =
        (ac_img (b Q) (ac_delta Q) ++
          ac_img (b (Q + 1)) (ac_delta (Q + 1))).getD ((i - 6 * Q) + 1) 0 := by
      have h' := hωu ((i - 6 * Q) + 1) (by omega)
      have e : i + 1 = 6 * Q + ((i - 6 * Q) + 1) := by omega
      rwa [← e] at h'
    have g2 : ac_omega b (i + 1 + 1) =
        (ac_img (b Q) (ac_delta Q) ++
          ac_img (b (Q + 1)) (ac_delta (Q + 1))).getD ((i - 6 * Q) + 2) 0 := by
      have h' := hωu ((i - 6 * Q) + 2) (by omega)
      have e : i + 1 + 1 = 6 * Q + ((i - 6 * Q) + 2) := by omega
      rwa [← e] at h'
    have n := ac_noaa_spec (ac_delta Q) (ac_delta (Q + 1)) (b Q) (b (Q + 1))
      (i - 6 * Q) hp10
    apply n
    constructor
    · rw [← g0, ← g1]
      exact h01.symm
    · rw [← g1, ← g2]
      exact h12.symm
  · have hℓ2 : 2 ≤ ℓ := by omega
    have h01 : i ≤ i + ℓ := by omega
    have h12 : i + ℓ ≤ i + 2 * ℓ := by omega
    have h23 : i + 2 * ℓ ≤ i + 3 * ℓ := by omega
    have hspan : 6 ≤ (i + 3 * ℓ) - i := by omega
    have c0 : (ac_cnt (ac_omega b) 0 (i + ℓ) (i + 2 * ℓ) : ℤ)
        - (ac_cnt (ac_omega b) 0 i (i + ℓ) : ℤ) = 0 := by
      have h := (hcube 0).1; omega
    have c1 : (ac_cnt (ac_omega b) 1 (i + ℓ) (i + 2 * ℓ) : ℤ)
        - (ac_cnt (ac_omega b) 1 i (i + ℓ) : ℤ) = 0 := by
      have h := (hcube 1).1; omega
    have c2 : (ac_cnt (ac_omega b) 2 (i + ℓ) (i + 2 * ℓ) : ℤ)
        - (ac_cnt (ac_omega b) 2 i (i + ℓ) : ℤ) = 0 := by
      have h := (hcube 2).1; omega
    have d0 : (ac_cnt (ac_omega b) 0 (i + 2 * ℓ) (i + 3 * ℓ) : ℤ)
        - (ac_cnt (ac_omega b) 0 (i + ℓ) (i + 2 * ℓ) : ℤ) = 0 := by
      have h := (hcube 0).2; omega
    have d1 : (ac_cnt (ac_omega b) 1 (i + 2 * ℓ) (i + 3 * ℓ) : ℤ)
        - (ac_cnt (ac_omega b) 1 (i + ℓ) (i + 2 * ℓ) : ℤ) = 0 := by
      have h := (hcube 1).2; omega
    have d2 : (ac_cnt (ac_omega b) 2 (i + 2 * ℓ) (i + 3 * ℓ) : ℤ)
        - (ac_cnt (ac_omega b) 2 (i + ℓ) (i + 2 * ℓ) : ℤ) = 0 := by
      have h := (hcube 2).2; omega
    have pd1 : ac_pdiff (ac_omega b) i (i + ℓ) (i + 2 * ℓ) = (0, 0, 0) :=
      Prod.ext c0 (Prod.ext c1 c2)
    have pd2 : ac_pdiff (ac_omega b) (i + ℓ) (i + 2 * ℓ) (i + 3 * ℓ) = (0, 0, 0) :=
      Prod.ext d0 (Prod.ext d1 d2)
    have hr : ac_realizes (ac_omega b)
        ((ac_omega b i, ac_omega b (i + ℓ), ac_omega b (i + 2 * ℓ),
          ac_omega b (i + 3 * ℓ)), ((0, 0, 0), (0, 0, 0)))
        i (i + ℓ) (i + 2 * ℓ) (i + 3 * ℓ) :=
      ⟨rfl, rfl, rfl, rfl, pd1, pd2⟩
    obtain ⟨p, hreal, hpos', hlt, m0, m1, m2, m3, hpar⟩ :=
      ac_descent (ac_omega b) ac_delta (fun q => ac_img (b q) (ac_delta q)) true
        (fun q => ac_img_length _ _) (fun q r hr => ac_omega_unfold b q r hr)
        (fun q => ac_img_memC _ _) (fun a q => ac_img_count _ _ _)
        _ i (i + ℓ) (i + 2 * ℓ) (i + 3 * ℓ) h01 h12 h23 hr hspan
    have hpmem : ac_T.contains p = true :=
      ac_zero_spec _ _ _ _ m0 m1 m2 m3 p hpar
    have hq01 : i / 6 ≤ (i + ℓ) / 6 := ac_div_mono h01
    have hq12 : (i + ℓ) / 6 ≤ (i + 2 * ℓ) / 6 := ac_div_mono h12
    have hq23 : (i + 2 * ℓ) / 6 ≤ (i + 3 * ℓ) / 6 := ac_div_mono h23
    exact ac_delta_no_T p hpmem (i / 6) ((i + ℓ) / 6) ((i + 2 * ℓ) / 6)
      ((i + 3 * ℓ) / 6) hq01 hq12 hq23 hpos' hreal

-- Singleton window count is an indicator.
private theorem ac_cnt_single (ω : ℕ → Fin 3) (a : Fin 3) (k : ℕ) :
    ac_cnt ω a k (k + 1) = (if ω k = a then 1 else 0) := by
  unfold ac_cnt
  have hsing : Finset.Ico k (k + 1) = {k} := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · intro hj; obtain ⟨hj1, hj2⟩ := hj; omega
    · intro hj; subst hj; exact ⟨le_refl _, Nat.lt_succ_self _⟩
  rw [hsing, Finset.filter_singleton]
  by_cases h : ω k = a <;> simp [h]

-- Strengthened: exact closed forms for all three letter counts.
private theorem ac_delta_count_all (j : ℕ) :
    12 * (ac_cnt ac_delta 0 0 (6 ^ j) : ℤ)
        = 5 * ((6 ^ j : ℕ) : ℤ) + 4 * ((3 ^ j : ℕ) : ℤ)
          + 3 * ((2 ^ j : ℕ) : ℤ) ∧
    12 * (ac_cnt ac_delta 1 0 (6 ^ j) : ℤ)
        = 3 * ((6 ^ j : ℕ) : ℤ) - 3 * ((2 ^ j : ℕ) : ℤ) ∧
    12 * (ac_cnt ac_delta 2 0 (6 ^ j) : ℤ)
        = 4 * ((6 ^ j : ℕ) : ℤ) - 4 * ((3 ^ j : ℕ) : ℤ) := by
  induction j with
  | zero =>
    have ne01 : (0 : Fin 3) ≠ 1 := by decide
    have ne02 : (0 : Fin 3) ≠ 2 := by decide
    have s0 : ac_cnt ac_delta 0 0 1 = 1 := by
      have h := ac_cnt_single ac_delta 0 0
      rw [ac_delta_zero] at h
      simp only [ite_true] at h
      exact h
    have s1 : ac_cnt ac_delta 1 0 1 = 0 := by
      have h := ac_cnt_single ac_delta 1 0
      rw [ac_delta_zero] at h
      simp only [ne01, ite_false] at h
      exact h
    have s2 : ac_cnt ac_delta 2 0 1 = 0 := by
      have h := ac_cnt_single ac_delta 2 0
      rw [ac_delta_zero] at h
      simp only [ne02, ite_false] at h
      exact h
    simp only [pow_zero, s0, s1, s2]
    norm_num
  | succ j ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    have e6 : (6 : ℕ) ^ (j + 1) = 6 * 6 ^ j := by rw [pow_succ, mul_comm]
    have r0 := ac_block_zero ac_delta ac_delta (fun q => ac_hImg (ac_delta q))
      (fun a c => (ac_hImg c).count a) (fun q => ac_hImg_len _)
      (fun q r hr => ac_delta_unfold q r hr) (fun a q => rfl) 0 (6 ^ j)
    have r1 := ac_block_zero ac_delta ac_delta (fun q => ac_hImg (ac_delta q))
      (fun a c => (ac_hImg c).count a) (fun q => ac_hImg_len _)
      (fun q r hr => ac_delta_unfold q r hr) (fun a q => rfl) 1 (6 ^ j)
    have r2 := ac_block_zero ac_delta ac_delta (fun q => ac_hImg (ac_delta q))
      (fun a c => (ac_hImg c).count a) (fun q => ac_hImg_len _)
      (fun q r hr => ac_delta_unfold q r hr) (fun a q => rfl) 2 (6 ^ j)
    rw [← e6] at r0 r1 r2
    have r0z : (ac_cnt ac_delta 0 0 (6 ^ (j + 1)) : ℤ)
        = 4 * (ac_cnt ac_delta 0 0 (6 ^ j) : ℤ)
          + 2 * (ac_cnt ac_delta 1 0 (6 ^ j) : ℤ)
          + (ac_cnt ac_delta 2 0 (6 ^ j) : ℤ) := by
      have h := congrArg (Nat.cast : ℕ → ℤ) r0
      push_cast at h
      rwa [ac_M_row0] at h
    have r1z : (ac_cnt ac_delta 1 0 (6 ^ (j + 1)) : ℤ)
        = (ac_cnt ac_delta 0 0 (6 ^ j) : ℤ)
          + 3 * (ac_cnt ac_delta 1 0 (6 ^ j) : ℤ)
          + (ac_cnt ac_delta 2 0 (6 ^ j) : ℤ) := by
      have h := congrArg (Nat.cast : ℕ → ℤ) r1
      push_cast at h
      rwa [ac_M_row1] at h
    have r2z : (ac_cnt ac_delta 2 0 (6 ^ (j + 1)) : ℤ)
        = (ac_cnt ac_delta 0 0 (6 ^ j) : ℤ)
          + (ac_cnt ac_delta 1 0 (6 ^ j) : ℤ)
          + 4 * (ac_cnt ac_delta 2 0 (6 ^ j) : ℤ) := by
      have h := congrArg (Nat.cast : ℕ → ℤ) r2
      push_cast at h
      rwa [ac_M_row2] at h
    have p6 : (((6 : ℕ) ^ (j + 1) : ℕ) : ℤ) = 6 * (((6 : ℕ) ^ j : ℕ) : ℤ) := by
      rw [pow_succ]; push_cast; ring
    have p3 : (((3 : ℕ) ^ (j + 1) : ℕ) : ℤ) = 3 * (((3 : ℕ) ^ j : ℕ) : ℤ) := by
      rw [pow_succ]; push_cast; ring
    have p2 : (((2 : ℕ) ^ (j + 1) : ℕ) : ℤ) = 2 * (((2 : ℕ) ^ j : ℕ) : ℤ) := by
      rw [pow_succ]; push_cast; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [r0z, p6, p3, p2]
      linear_combination 4 * ih0 + 2 * ih1 + ih2
    · rw [r1z, p6, p2]
      linear_combination ih0 + 3 * ih1 + ih2
    · rw [r2z, p6, p3]
      linear_combination ih0 + ih1 + 4 * ih2

-- Density of letter 1 in δ.
private theorem ac_delta_one_pow (j : ℕ) :
    4 * ac_cnt ac_delta 1 0 (6 ^ j) + 2 ^ j = 6 ^ j := by
  have h := (ac_delta_count_all j).2.1
  omega

private theorem ac_cnt_le_length (ω : ℕ → Fin 3) (a : Fin 3) (i j : ℕ) :
    ac_cnt ω a i j ≤ j - i := by
  unfold ac_cnt
  calc ((Finset.Ico i j).filter (fun k => ω k = a)).card
      ≤ (Finset.Ico i j).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = j - i := Nat.card_Ico i j

private theorem ac_cnt_zero_empty (ω : ℕ → Fin 3) (a : Fin 3) (i : ℕ) :
    ac_cnt ω a i i = 0 := by
  unfold ac_cnt
  simp

private theorem ac_cnt_block_sum (ω : ℕ → Fin 3) (a : Fin 3) (m q : ℕ) :
    ac_cnt ω a 0 (q * m) =
      ∑ i ∈ Finset.range q, ac_cnt ω a (i * m) ((i + 1) * m) := by
  induction q with
  | zero =>
    simp [ac_cnt_zero_empty]
  | succ q ih =>
    have hmul : (q + 1) * m = q * m + m := by ring
    have hle : q * m ≤ (q + 1) * m := by omega
    have hsplit := ac_cnt_split (ω := ω) (a := a) (i := 0) (j := q * m)
      (k := (q + 1) * m) (Nat.zero_le _) hle
    rw [hsplit, ih, Finset.sum_range_succ]

private theorem ac_lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpos : 0 < 2 ^ n := pow_pos (by omega) _
    have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    have hle : n + 1 ≤ 2 ^ n := ih
    rw [hpow]
    omega

private theorem ac_two_pow_le_three_pow (n : ℕ) : 2 ^ n ≤ 3 ^ n := by
  gcongr
  omega

private theorem ac_six_pow_eq (j : ℕ) : 6 ^ j = 2 ^ j * 3 ^ j := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, mul_pow]

-- Good window with many ones.
private theorem ac_good_window (m : ℕ) :
    ∃ s, m ≤ 4 * ac_cnt ac_delta 1 s (s + m) + 3 := by
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨0, by omega⟩
  · by_cases hm3 : m ≤ 3
    · exact ⟨0, by omega⟩
    · have hm4 : 4 ≤ m := by omega
      have hmpos : 0 < m := by omega
      set K : ℕ := 3 * m ^ 2 + m with hKdef
      set j : ℕ := K + 1 with hjdef
      have hj_gt_K : K < j := by omega
      have h2j_gt : K < 2 ^ j := lt_trans hj_gt_K (ac_lt_two_pow_self j)
      by_contra hcon
      simp only [not_exists] at hcon
      have hbad : ∀ s, 4 * ac_cnt ac_delta 1 s (s + m) + 3 < m := by
        intro s
        have h := hcon s
        omega
      have hblock4 : ∀ i, 4 * ac_cnt ac_delta 1 (i * m) ((i + 1) * m) + 4 ≤ m := by
        intro i
        have h := hbad (i * m)
        have heq : i * m + m = (i + 1) * m := by ring
        rw [heq] at h
        omega
      set N : ℕ := 6 ^ j with hNdef
      set q : ℕ := N / m with hqdef
      set r : ℕ := N % m with hrdef
      have hdiv : q * m + r = N := by
        rw [hqdef, hrdef, Nat.mul_comm (N / m) m]
        exact Nat.div_add_mod N m
      have hmod : r < m := Nat.mod_lt N hmpos
      have hqm_le : q * m ≤ N := by omega
      have hT0 := ac_delta_one_pow j
      rw [← hNdef] at hT0
      have hsplit := ac_cnt_split (ω := ac_delta) (a := 1) (i := 0) (j := q * m)
        (k := N) (Nat.zero_le _) hqm_le
      have hsum := ac_cnt_block_sum ac_delta 1 m q
      have hsum_le : ∑ i ∈ Finset.range q,
          (4 * ac_cnt ac_delta 1 (i * m) ((i + 1) * m) + 4) ≤
          ∑ _i ∈ Finset.range q, m := by
        apply Finset.sum_le_sum
        intro i _
        exact hblock4 i
      rw [Finset.sum_add_distrib] at hsum_le
      have hconst_m : (∑ _i ∈ Finset.range q, m) = q * m := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hconst_4 : (∑ _i ∈ Finset.range q, 4) = 4 * q := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      have hmul_sum : (∑ i ∈ Finset.range q,
          4 * ac_cnt ac_delta 1 (i * m) ((i + 1) * m)) =
          4 * ac_cnt ac_delta 1 0 (q * m) := by
        rw [hsum, Finset.mul_sum]
      rw [hconst_m, hconst_4, hmul_sum] at hsum_le
      have hcnt_last_le : ac_cnt ac_delta 1 (q * m) N ≤ r := by
        have hle := ac_cnt_le_length ac_delta 1 (q * m) N
        have hr_eq : N - q * m = r := by omega
        rw [hr_eq] at hle
        exact hle
      have h4last : 4 * ac_cnt ac_delta 1 (q * m) N ≤ 4 * r := by omega
      have hmain : N + 4 * q ≤ q * m + 4 * r + 2 ^ j := by omega
      have h4q : 4 * q ≤ 3 * r + 2 ^ j := by omega
      have eN : ((N : ℕ) : ℤ) = ((2 ^ j : ℕ) : ℤ) * ((3 ^ j : ℕ) : ℤ) := by
        rw [hNdef]
        exact_mod_cast ac_six_pow_eq j
      have zdiv : ((q : ℕ) : ℤ) * ((m : ℕ) : ℤ) + ((r : ℕ) : ℤ) =
          ((N : ℕ) : ℤ) := by
        exact_mod_cast hdiv
      have z4q : 4 * ((q : ℕ) : ℤ) ≤ 3 * ((r : ℕ) : ℤ) + ((2 ^ j : ℕ) : ℤ) := by
        exact_mod_cast h4q
      have zm : (0 : ℤ) ≤ ((m : ℕ) : ℤ) := Nat.cast_nonneg m
      have h7 : ((m : ℕ) : ℤ) * (4 * ((q : ℕ) : ℤ)) ≤
          ((m : ℕ) : ℤ) * (3 * ((r : ℕ) : ℤ) + ((2 ^ j : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_left z4q zm
      have h2K : (((3 * m ^ 2 + m : ℕ)) : ℤ) < ((2 ^ j : ℕ) : ℤ) := by
        have h : K < 2 ^ j := h2j_gt
        rw [hKdef] at h
        exact_mod_cast h
      have hr2 : ((2 ^ j : ℕ) : ℤ) ≤ ((3 ^ j : ℕ) : ℤ) := by
        exact_mod_cast ac_two_pow_le_three_pow j
      have hrm : ((r : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) - 1 := by
        have h : r + 1 ≤ m := hmod
        have h' : ((r : ℕ) : ℤ) + 1 ≤ ((m : ℕ) : ℤ) := by exact_mod_cast h
        linarith
      have key : ((2 ^ j : ℕ) : ℤ) * (4 * ((3 ^ j : ℕ) : ℤ) - ((m : ℕ) : ℤ)) ≤
          ((r : ℕ) : ℤ) * (3 * ((m : ℕ) : ℤ) + 4) := by
        nlinarith [h7, zdiv, eN]
      have hpos : (0 : ℤ) < 4 * ((3 ^ j : ℕ) : ℤ) - ((m : ℕ) : ℤ) := by
        nlinarith [h2K, hr2, pow_nonneg zm 2, zm]
      have hone : (1 : ℤ) ≤ 4 * ((3 ^ j : ℕ) : ℤ) - ((m : ℕ) : ℤ) := by
        have h := Int.add_one_le_of_lt hpos
        simpa using h
      have ht2nn : (0 : ℤ) ≤ ((2 ^ j : ℕ) : ℤ) := Nat.cast_nonneg _
      have hbig : ((2 ^ j : ℕ) : ℤ) ≤ ((2 ^ j : ℕ) : ℤ) *
          (4 * ((3 ^ j : ℕ) : ℤ) - ((m : ℕ) : ℤ)) := by
        calc ((2 ^ j : ℕ) : ℤ) = ((2 ^ j : ℕ) : ℤ) * 1 := by ring
          _ ≤ ((2 ^ j : ℕ) : ℤ) * (4 * ((3 ^ j : ℕ) : ℤ) - ((m : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_left hone ht2nn
      have hnn : (0 : ℤ) ≤ 3 * ((m : ℕ) : ℤ) + 4 := by
        have h := zm
        linarith
      have hsmall : ((r : ℕ) : ℤ) * (3 * ((m : ℕ) : ℤ) + 4) ≤
          (((m : ℕ) : ℤ) - 1) * (3 * ((m : ℕ) : ℤ) + 4) :=
        mul_le_mul_of_nonneg_right hrm hnn
      have hexpand : (((m : ℕ) : ℤ) - 1) * (3 * ((m : ℕ) : ℤ) + 4) =
          3 * ((m : ℕ) : ℤ) ^ 2 + ((m : ℕ) : ℤ) - 4 := by ring
      have hcast : (((3 * m ^ 2 + m : ℕ)) : ℤ) =
          3 * ((m : ℕ) : ℤ) ^ 2 + ((m : ℕ) : ℤ) := by push_cast; ring
      have hlt : (((m : ℕ) : ℤ) - 1) * (3 * ((m : ℕ) : ℤ) + 4) <
          ((2 ^ j : ℕ) : ℤ) := by
        rw [hexpand, ← hcast]
        linarith [h2K]
      linarith [hbig, key, hsmall, hlt]

-- 2^(#ones) lower bound on the ncard.
set_option maxHeartbeats 1000000 in
private theorem ac_ncard_lower (n s : ℕ) :
    2 ^ ((Finset.Ico s (s + n / 6)).filter (fun q => ac_delta q = 1)).card ≤
      Set.ncard {w : List (Fin 3) | w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} := by
  have himg0 : (ac_img true 1).getD 0 0 = 0 := by decide
  have himg2 : (ac_img false 1).getD 0 0 = 2 := by decide
  set F : Finset ℕ → List (Fin 3) := fun S =>
    List.ofFn (fun k : Fin n => ac_omega (fun q => decide (q ∈ S)) (6 * s + (k : ℕ)))
    with hFdef
  set Q : Finset ℕ := (Finset.Ico s (s + n / 6)).filter
    (fun q => ac_delta q = 1) with hQdef
  have hQmem : ∀ q : ℕ, q ∈ Q → s ≤ q ∧ q < s + n / 6 ∧ ac_delta q = 1 := by
    intro q hq
    rw [hQdef] at hq
    rw [Finset.mem_filter, Finset.mem_Ico] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2⟩
  have h6m : 6 * (n / 6) ≤ n := by omega
  have hidx : ∀ q : ℕ, q ∈ Q → 6 * (q - s) < n := by
    intro q hq
    obtain ⟨hlo, hhi, -⟩ := hQmem q hq
    omega
  have hget : ∀ (S : Finset ℕ) (q : ℕ) (hq : q ∈ Q),
      (F S).getD (6 * (q - s)) 0 =
        (ac_img (decide (q ∈ S)) 1).getD 0 0 := by
    intro S q hq
    obtain ⟨hlo, -, hδ⟩ := hQmem q hq
    have h65 : 6 * s + 6 * (q - s) = 6 * q := by omega
    have hlen : 6 * (q - s) < (List.ofFn (fun k : Fin n =>
        ac_omega (fun q => decide (q ∈ S)) (6 * s + (k : ℕ)))).length := by
      rw [List.length_ofFn]
      exact hidx q hq
    have hhl := List.getElem_ofFn (f := fun k : Fin n =>
      ac_omega (fun q => decide (q ∈ S)) (6 * s + (k : ℕ))) hlen
    have hunf : ac_omega (fun q => decide (q ∈ S)) (6 * q + 0) =
        (ac_img (decide (q ∈ S)) (ac_delta q)).getD 0 0 :=
      ac_omega_unfold _ _ _ (by decide)
    have h60 : 6 * q = 6 * q + 0 := by omega
    have h2 : ac_omega (fun q => decide (q ∈ S)) (6 * s + 6 * (q - s)) =
        (ac_img (decide (q ∈ S)) 1).getD 0 0 := by
      rw [h65, h60, hunf, hδ]
    have hFS : F S = List.ofFn (fun k : Fin n =>
        ac_omega (fun q => decide (q ∈ S)) (6 * s + (k : ℕ))) := rfl
    rw [hFS, List.getD_eq_getElem _ _ hlen]
    exact hhl.trans h2
  have hdisc : ∀ (S : Finset ℕ) (q : ℕ) (hq : q ∈ Q),
      ((F S).getD (6 * (q - s)) 0 = 0) ↔ q ∈ S := by
    intro S q hq
    rw [hget S q hq]
    by_cases h : q ∈ S
    · have e : decide (q ∈ S) = true := by simp [h]
      rw [e, himg0]
      exact iff_of_true rfl h
    · have e : decide (q ∈ S) = false := by simp [h]
      rw [e, himg2]
      exact iff_of_false (by decide) h
  have hFmem : ∀ S ∈ Q.powerset, F S ∈ {w : List (Fin 3) | w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} := by
    intro S _
    constructor
    · have hlen : (F S).length = n := List.length_ofFn
      exact hlen
    · rintro ⟨p, x, y, z, t, hfac, hx, hy, hz, heq⟩
      have hfac' : List.ofFn (fun k : Fin n =>
          ac_omega (fun q => decide (q ∈ S)) (6 * s + (k : ℕ))) =
          p ++ x ++ y ++ z ++ t := hfac
      have hbr := ac_list_factor_bridge (ac_omega fun q => decide (q ∈ S)) (6 * s) n
        (List.ofFn fun k : Fin n => ac_omega (fun q => decide (q ∈ S)) (6 * s + ↑k))
        rfl p x y z t hfac' hx hy hz (fun a => (heq a).1) (fun a => (heq a).2)
      obtain ⟨hℓ, hyl, hzl, hcounts⟩ := hbr
      have hcon := ac_omega_cubeFree (fun q => decide (q ∈ S))
        (6 * s + p.length) x.length hℓ
      apply hcon
      intro a
      obtain ⟨e1, e2⟩ := hcounts a
      rw [hyl] at e1
      rw [hyl, hzl] at e2
      refine ⟨?_, ?_⟩
      · have j1 : 6 * s + (p.length + x.length) =
            6 * s + p.length + x.length := by omega
        have j2 : 6 * s + p.length + x.length + x.length =
            6 * s + p.length + 2 * x.length := by omega
        rw [j1, j2] at e1
        exact e1
      · have k1 : 6 * s + (p.length + x.length) =
            6 * s + p.length + x.length := by omega
        have k2 : 6 * s + p.length + x.length + x.length =
            6 * s + p.length + 2 * x.length := by omega
        have k3 : 6 * s + ((p.length + x.length) + x.length) =
            6 * s + p.length + 2 * x.length := by omega
        have k4 : 6 * s + p.length + 2 * x.length + x.length =
            6 * s + p.length + 3 * x.length := by omega
        rw [k1, k2, k3, k4] at e2
        exact e2
  have hinj : Set.InjOn F (↑(Q.powerset) : Set (Finset ℕ)) := by
    intro S hS T hT hST
    have hSQ : S ⊆ Q := Finset.mem_powerset.mp (Finset.mem_coe.mp hS)
    have hTQ : T ⊆ Q := Finset.mem_powerset.mp (Finset.mem_coe.mp hT)
    ext q
    by_cases hqQ : q ∈ Q
    · have eS := hdisc S q hqQ
      have eT := hdisc T q hqQ
      rw [hST] at eS
      exact eS.symm.trans eT
    · have hSq : q ∉ S := fun h => hqQ (hSQ h)
      have hTq : q ∉ T := fun h => hqQ (hTQ h)
      exact iff_of_false hSq hTq
  have hfin : Set.Finite {w : List (Fin 3) | w.length = n ∧
      ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
        x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
        ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} :=
    (List.finite_length_eq (Fin 3) n).subset (fun w hw => hw.1)
  have hmem_image : F '' (↑(Q.powerset) : Set (Finset ℕ)) ⊆ {w : List (Fin 3) |
      w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} := by
    rintro w ⟨S, hS, rfl⟩
    exact hFmem S (Finset.mem_coe.mp hS)
  have hcard : (Finset.image F Q.powerset).card = 2 ^ Q.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  have hcoe : F '' (↑(Q.powerset) : Set (Finset ℕ)) =
      ↑(Finset.image F Q.powerset) := Finset.coe_image.symm
  have hle : Set.ncard (F '' ↑(Q.powerset)) ≤ Set.ncard {w : List (Fin 3) |
      w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} :=
    Set.ncard_le_ncard hmem_image hfin
  rw [hcoe, Set.ncard_coe_finset, hcard] at hle
  exact hle

/-- **Exponential lower bound for ternary abelian-cube-free words.** An abelian cube is a word
$xyz$ with $x$, $y$, $z$ nonempty such that each letter occurs equally often in $x$, $y$ and $z$.
Let $a_n$ be the number of words of length $n$ over $\{0, 1, 2\}$ that contain no abelian cube
as a factor. Then $2^{n/24} = O(a_n)$ as $n \to \infty$: there is a constant $C$ such that
$2^{n/24} \le C a_n$ for all sufficiently large $n$.

Source: Ali Aberkane and James D. Currie, *The Number of Ternary Words
Avoiding Abelian Cubes Grows Exponentially*, Journal of Integer Sequences 7
(2004), Article 04.2.7,
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Currie/currie18.tex>,
Second Main Theorem, lines 558-561.
-/
theorem abelianCubeFree :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 24))
      (fun n : ℕ => ((Set.ncard {w : List (Fin 3) | w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a}) : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨s, hs⟩ := ac_good_window (n / 6)
  have hlow := ac_ncard_lower n s
  set Q : Finset ℕ := (Finset.Ico s (s + n / 6)).filter
    (fun q => ac_delta q = 1) with hQdef
  have hQcard : Q.card = ac_cnt ac_delta 1 s (s + n / 6) := rfl
  rw [← hQcard] at hs
  have hn6 : n ≤ 6 * (n / 6) + 5 := by omega
  have hbound : n ≤ 24 * Q.card + 23 := by omega
  have hA : ((2 ^ Q.card : ℕ) : ℝ) ≤
      ((Set.ncard {w : List (Fin 3) | w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} : ℕ) : ℝ) := by
    exact_mod_cast hlow
  have hexp : (n : ℝ) / 24 ≤ ((Q.card : ℕ) : ℝ) + 1 := by
    have h : ((n : ℕ) : ℝ) ≤ 24 * ((Q.card : ℕ) : ℝ) + 23 := by
      exact_mod_cast hbound
    linarith
  have hrpow_le : (2 : ℝ) ^ ((n : ℝ) / 24) ≤
      (2 : ℝ) ^ (((Q.card : ℕ) : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hrpow_eq : (2 : ℝ) ^ (((Q.card : ℕ) : ℝ) + 1) =
      2 * (((2 ^ Q.card : ℕ)) : ℝ) := by
    have hMC : (2 : ℝ) ^ Q.card = (((2 ^ Q.card : ℕ)) : ℝ) := by norm_cast
    calc (2 : ℝ) ^ (((Q.card : ℕ) : ℝ) + 1)
        = (2 : ℝ) ^ (((Q.card : ℕ) : ℝ)) * 2 := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
      _ = (((2 ^ Q.card : ℕ)) : ℝ) * 2 := by rw [Real.rpow_natCast, hMC]
      _ = 2 * (((2 ^ Q.card : ℕ)) : ℝ) := by ring
  have hnn1 : (0 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 24) :=
    Real.rpow_nonneg (by norm_num) _
  have hnn2 : (0 : ℝ) ≤ (((Set.ncard {w : List (Fin 3) | w.length = n ∧
      ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
        x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
        ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} : ℕ)) : ℝ) :=
    Nat.cast_nonneg _
  change ‖(2 : ℝ) ^ ((n : ℝ) / 24)‖ ≤ 2 * ‖((((Set.ncard {w : List (Fin 3) |
      w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} : ℕ)) : ℝ))‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
  calc (2 : ℝ) ^ ((n : ℝ) / 24) ≤ (2 : ℝ) ^ (((Q.card : ℕ) : ℝ) + 1) := hrpow_le
    _ = 2 * (((2 ^ Q.card : ℕ)) : ℝ) := hrpow_eq
    _ ≤ 2 * (((Set.ncard {w : List (Fin 3) | w.length = n ∧
        ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
          x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
          ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a} : ℕ)) : ℝ) :=
        mul_le_mul_of_nonneg_left hA (by norm_num)

end
end MetaMathlibExt
