/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Bell permutations of the second kind
-/

/-- Restricted growth function condition. -/
private def IsRGF {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ i : Fin n, ∀ j : Fin n, j.val < (f i).val → ∃ i₀ : Fin n, i₀.val < i.val ∧ f i₀ = j
/-- The Bell permutation of the second kind associated to `f`. -/
private def bellPerm {n : ℕ} (f : Fin n → Fin n) : Equiv.Perm (Fin n) :=
  ((List.finRange n).map fun i => Equiv.swap i (f i)).prod
/-- Number of weak excedances of a permutation. -/
private def numWeak {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  Fintype.card {i : Fin n // i ≤ σ i}
/-- `f` never exceeds the identity. -/
private def Subdiag {n : ℕ} (f : Fin n → Fin n) : Prop := ∀ i : Fin n, (f i).val ≤ i.val
/-- Number of distinct values of `f`. -/
private def numVals {n : ℕ} (f : Fin n → Fin n) : ℕ := (Finset.univ.image f).card

/-! ## Every RGF is subdiagonal -/

private theorem rgf_subdiag {n : ℕ} {f : Fin n → Fin n} (hf : IsRGF f) : Subdiag f := by
  intro i
  by_contra h
  simp only [not_le] at h
  have hle : (f i).val ≤ i.val → False := by omega
  apply hle
  classical
  have inj : ∀ x : Fin ((f i).val), ∃ i₀ : Fin n, i₀.val < i.val ∧ f i₀ = ⟨x.val, by omega⟩ := by
    intro x
    exact hf i ⟨x.val, by omega⟩ (by simp)
  choose g hg1 hg2 using inj
  have ginj : Function.Injective (fun x : Fin ((f i).val) => (⟨(g x).val, hg1 x⟩ : Fin i.val)) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    have hgab : g a = g b := Fin.ext hab
    have hval : (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ := by
      rw [← hg2 a, ← hg2 b, hgab]
    exact Fin.ext (by simpa using congrArg Fin.val hval)
  have := Fintype.card_le_of_injective _ ginj
  simpa using this

/-! ## Contiguity: the value set of an RGF is an initial segment -/

private theorem downward_closed_card {n : ℕ} (s : Finset (Fin n))
    (hdc : ∀ v w : Fin n, v ∈ s → w.val < v.val → w ∈ s) (v : Fin n) :
    v ∈ s ↔ v.val < s.card := by
  constructor
  · intro hv
    have hsub : Finset.Iic v ⊆ s := by
      intro w hw
      rw [Finset.mem_Iic, Fin.le_def] at hw
      rcases lt_or_eq_of_le hw with h | h
      · exact hdc v w hv h
      · have : w = v := Fin.ext h
        rwa [this]
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra hv
    have hsub : s ⊆ Finset.Iio v := by
      intro w hw
      rw [Finset.mem_Iio, Fin.lt_def]
      rcases lt_trichotomy w.val v.val with h | h | h
      · exact h
      · have hwv : w = v := Fin.ext h
        exact absurd (hwv ▸ hw) hv
      · exact absurd (hdc w v hw h) hv
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

private theorem rgf_mem_image {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin n) :
    v ∈ Finset.univ.image g ↔ v.val < numVals g := by
  apply downward_closed_card
  intro a b ha hab
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha ⊢
  obtain ⟨i, hi⟩ := ha
  obtain ⟨i₀, _, hi₀⟩ := hg i b (by rw [hi]; exact hab)
  exact ⟨i₀, hi₀⟩

private theorem numVals_le {n : ℕ} (g : Fin n → Fin n) : numVals g ≤ n := by
  unfold numVals
  calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-! ## Part A: `bellPerm` is injective on RGFs -/

/-- Partial product of the first `m` swaps. -/
private def pp {n : ℕ} (f : Fin n → Fin n) (m : ℕ) : Equiv.Perm (Fin n) :=
  (((List.finRange n).take m).map (fun i => Equiv.swap i (f i))).prod

private theorem pp_zero {n : ℕ} (f : Fin n → Fin n) : pp f 0 = 1 := by
  simp [pp]

private theorem pp_succ {n : ℕ} (f : Fin n → Fin n) {m : ℕ} (h : m < n) :
    pp f (m+1) = pp f m * Equiv.swap ⟨m, h⟩ (f ⟨m, h⟩) := by
  have hlen : m < (List.finRange n).length := by simpa using h
  have : (List.finRange n).take (m+1) = (List.finRange n).take m ++ [(⟨m, h⟩ : Fin n)] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getElem?_eq_getElem hlen, List.getElem_finRange]
    simp
  unfold pp
  rw [this, List.map_append, List.prod_append]
  simp

private theorem pp_full {n : ℕ} (f : Fin n → Fin n) : pp f n = bellPerm f := by
  unfold pp bellPerm
  rw [List.take_of_length_le (by simp)]

private theorem pp_fixes {n : ℕ} {f : Fin n → Fin n} (hf : Subdiag f) :
    ∀ (m : ℕ) (j : Fin n), m ≤ j.val → pp f m j = j := by
  intro m
  induction m with
  | zero => intro j _; rw [pp_zero]; rfl
  | succ m ih =>
    intro j hj
    have hmn : m < n := by have := j.isLt; omega
    rw [pp_succ f hmn, Equiv.Perm.mul_apply]
    have hne1 : j ≠ (⟨m, hmn⟩ : Fin n) := by
      intro hc
      have : j.val = m := by rw [hc]
      omega
    have hne2 : j ≠ f ⟨m, hmn⟩ := by
      intro hc
      have h1 : (f ⟨m, hmn⟩).val ≤ m := hf ⟨m, hmn⟩
      have : j.val = (f ⟨m, hmn⟩).val := by rw [hc]
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    exact ih j (by omega)

private theorem pp_succ_apply {n : ℕ} {f : Fin n → Fin n} (hf : Subdiag f) {m : ℕ} (h : m < n) :
    pp f (m+1) (f ⟨m, h⟩) = ⟨m, h⟩ := by
  rw [pp_succ f h, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  exact pp_fixes hf m ⟨m, h⟩ (le_refl m)

private theorem pp_eq_imp {n : ℕ} {f g : Fin n → Fin n} (hf : Subdiag f) (hg : Subdiag g) :
    ∀ (m : ℕ), m ≤ n → pp f m = pp g m → ∀ i : Fin n, i.val < m → f i = g i := by
  intro m
  induction m with
  | zero => intro _ _ i hi; omega
  | succ m ih =>
    intro hmn heq i hi
    have hm : m < n := by omega
    have e1 : pp f (m+1) (f ⟨m, hm⟩) = ⟨m, hm⟩ := pp_succ_apply hf hm
    have e2 : pp g (m+1) (g ⟨m, hm⟩) = ⟨m, hm⟩ := pp_succ_apply hg hm
    have e2' : pp f (m+1) (g ⟨m, hm⟩) = ⟨m, hm⟩ := by rw [heq]; exact e2
    have htop : f ⟨m, hm⟩ = g ⟨m, hm⟩ := (pp f (m+1)).injective (e1.trans e2'.symm)
    have hswap : Equiv.swap (⟨m, hm⟩ : Fin n) (f ⟨m, hm⟩) = Equiv.swap ⟨m, hm⟩ (g ⟨m, hm⟩) := by
      rw [htop]
    have hppm : pp f m = pp g m := by
      rw [pp_succ f hm, pp_succ g hm, hswap] at heq
      exact mul_right_cancel heq
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heqi
    · exact ih (by omega) hppm i hlt
    · have : i = ⟨m, hm⟩ := Fin.ext (by omega)
      rw [this]; exact htop

private theorem bellPerm_inj_subdiag {n : ℕ} {f g : Fin n → Fin n} (hf : Subdiag f) (hg : Subdiag g)
    (h : bellPerm f = bellPerm g) : f = g := by
  have hn : pp f n = pp g n := by rw [pp_full, pp_full]; exact h
  funext i
  exact pp_eq_imp hf hg n (le_refl n) hn i i.isLt

/-! ## Part B: `numWeak (bellPerm f) = numVals f` -/

/-- Suffix product of the swaps with index `≥ m`. -/
private def qq {n : ℕ} (f : Fin n → Fin n) (m : ℕ) : Equiv.Perm (Fin n) :=
  (((List.finRange n).drop m).map (fun i => Equiv.swap i (f i))).prod

private theorem qq_zero {n : ℕ} (f : Fin n → Fin n) : qq f 0 = bellPerm f := by
  simp [qq, bellPerm]

private theorem qq_ge {n : ℕ} (f : Fin n → Fin n) {m : ℕ} (h : n ≤ m) : qq f m = 1 := by
  unfold qq
  rw [List.drop_of_length_le (by simpa using h)]
  simp

private theorem qq_succ {n : ℕ} (f : Fin n → Fin n) {m : ℕ} (h : m < n) :
    qq f m = Equiv.swap ⟨m, h⟩ (f ⟨m, h⟩) * qq f (m+1) := by
  have hlen : m < (List.finRange n).length := by simpa using h
  have hdrop : (List.finRange n).drop m = (⟨m, h⟩ : Fin n) :: (List.finRange n).drop (m+1) := by
    rw [List.drop_eq_getElem_cons hlen, List.getElem_finRange]
    simp
  unfold qq
  rw [hdrop, List.map_cons, List.prod_cons]

private theorem qq_fix {n : ℕ} (f : Fin n → Fin n) (y : Fin n) :
    ∀ d m : ℕ, n - m ≤ d → (∀ i : Fin n, m ≤ i.val → y ≠ i ∧ y ≠ f i) → qq f m y = y := by
  intro d
  induction d with
  | zero => intro m hm _; rw [qq_ge f (by omega)]; rfl
  | succ d ih =>
    intro m hm H
    by_cases hmn : n ≤ m
    · rw [qq_ge f hmn]; rfl
    · rw [not_le] at hmn
      rw [qq_succ f hmn, Equiv.Perm.mul_apply]
      have hrec : qq f (m+1) y = y := ih (m+1) (by omega) (fun i hi => H i (by omega))
      rw [hrec]
      obtain ⟨h1, h2⟩ := H ⟨m, hmn⟩ (le_refl m)
      exact Equiv.swap_apply_of_ne_of_ne h1 h2

private theorem qq_lower_const {n : ℕ} (f : Fin n → Fin n) (y z : Fin n) (m0 : ℕ) (hm0 : m0 < n)
    (hz : qq f m0 y = z) (Hfix : ∀ i : Fin n, i.val < m0 → z ≠ i ∧ z ≠ f i) :
    qq f 0 y = z := by
  have key : ∀ d m, m0 - m ≤ d → m ≤ m0 → qq f m y = z := by
    intro d
    induction d with
    | zero =>
      intro m h1 h2
      obtain rfl : m = m0 := by omega
      exact hz
    | succ d ih =>
      intro m h1 h2
      rcases eq_or_lt_of_le h2 with heq | hlt
      · subst heq; exact hz
      · have hmn : m < n := by omega
        rw [qq_succ f hmn, Equiv.Perm.mul_apply, ih (m+1) (by omega) (by omega)]
        obtain ⟨ha, hb⟩ := Hfix ⟨m, hmn⟩ hlt
        exact Equiv.swap_apply_of_ne_of_ne ha hb
  exact key m0 0 (by omega) (by omega)

private theorem sigma_ge_of_value {n : ℕ} {f : Fin n → Fin n} (hf : Subdiag f) (v : Fin n)
    (hv : ∃ j, f j = v) : v ≤ bellPerm f v := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => f i = v)
  have hSne : S.Nonempty := by obtain ⟨j, hj⟩ := hv; exact ⟨j, by simp [S, hj]⟩
  let mp := S.max' hSne
  have hmpf : f mp = v := by
    have : mp ∈ S := S.max'_mem hSne
    simpa [S] using this
  have hmpmax : ∀ i, f i = v → i ≤ mp := by
    intro i hi; exact S.le_max' i (by simp [S, hi])
  have hvmp : v.val ≤ mp.val := by
    have := hf mp; rw [hmpf] at this; exact this
  have fixhi : qq f (mp.val + 1) v = v := by
    apply qq_fix f v n (mp.val + 1) (by omega)
    intro i hi
    constructor
    · intro hc; rw [← hc] at hi; omega
    · intro hc
      have := hmpmax i hc.symm
      have : i.val ≤ mp.val := this
      omega
  have hbase : qq f mp.val v = mp := by
    have hmn : mp.val < n := mp.isLt
    rw [qq_succ f hmn, Equiv.Perm.mul_apply, fixhi]
    have hmm : (⟨mp.val, hmn⟩ : Fin n) = mp := Fin.ext rfl
    rw [hmm, hmpf, Equiv.swap_apply_right]
  have hσ : bellPerm f v = mp := by
    rw [← qq_zero]
    apply qq_lower_const f v mp mp.val mp.isLt hbase
    intro i hi
    constructor
    · intro hc; rw [hc] at hi; omega
    · intro hc
      have hle := hf i
      rw [← hc] at hle
      have : mp.val ≤ i.val := hle
      omega
  rw [hσ]
  exact hvmp

private theorem sigma_lt_of_novalue {n : ℕ} {f : Fin n → Fin n} (x : Fin n)
    (Hlt : ∀ i : Fin n, (f i).val < x.val) : (bellPerm f x).val < x.val := by
  have fixhi : qq f (x.val + 1) x = x := by
    apply qq_fix f x n (x.val + 1) (by omega)
    intro i hi
    refine ⟨?_, ?_⟩
    · intro hc; rw [← hc] at hi; omega
    · intro hc; have := Hlt i; rw [hc] at this; omega
  have hbase : (qq f x.val x).val < x.val := by
    have hxn := x.isLt
    rw [qq_succ f hxn, Equiv.Perm.mul_apply, fixhi]
    have hxx : (⟨x.val, hxn⟩ : Fin n) = x := Fin.ext rfl
    rw [hxx, Equiv.swap_apply_left]
    exact Hlt x
  have key : ∀ d m, x.val - m ≤ d → m ≤ x.val → (qq f m x).val < x.val := by
    intro d
    induction d with
    | zero =>
      intro m h1 h2
      obtain rfl : m = x.val := by omega
      exact hbase
    | succ d ih =>
      intro m h1 h2
      rcases eq_or_lt_of_le h2 with heq | hlt
      · rw [heq]; exact hbase
      · have hmn : m < n := by omega
        rw [qq_succ f hmn, Equiv.Perm.mul_apply]
        have hw : (qq f (m+1) x).val < x.val := ih (m+1) (by omega) (by omega)
        rcases eq_or_ne (qq f (m+1) x) ⟨m, hmn⟩ with h | h
        · rw [h, Equiv.swap_apply_left]; exact Hlt _
        rcases eq_or_ne (qq f (m+1) x) (f ⟨m, hmn⟩) with h' | h'
        · rw [h', Equiv.swap_apply_right]; exact hlt
        · rw [Equiv.swap_apply_of_ne_of_ne h h']; exact hw
  have := key x.val 0 (by omega) (by omega)
  rwa [qq_zero] at this

private theorem rgf_novalue_lt {n : ℕ} {f : Fin n → Fin n} (hf : IsRGF f) (x : Fin n)
    (hx : ∀ j, f j ≠ x) : ∀ j, (f j).val < x.val := by
  intro j
  rcases lt_trichotomy (f j).val x.val with h | h | h
  · exact h
  · exact absurd (Fin.ext h) (hx j)
  · obtain ⟨i0, _, hi0⟩ := hf j x h
    exact absurd hi0 (hx i0)

private theorem numWeak_bellPerm {n : ℕ} {f : Fin n → Fin n} (hf : IsRGF f) :
    numWeak (bellPerm f) = numVals f := by
  have hsd := rgf_subdiag hf
  have hset : Finset.univ.filter (fun i => i ≤ bellPerm f i) = Finset.univ.image f := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      by_contra hc
      simp only [not_exists] at hc
      have hlt := sigma_lt_of_novalue i (rgf_novalue_lt hf i hc)
      have hi' : i.val ≤ (bellPerm f i).val := hi
      omega
    · rintro ⟨j, hj⟩
      exact sigma_ge_of_value hsd i ⟨j, hj⟩
  unfold numWeak numVals
  rw [Fintype.card_subtype, hset]

/-! ## Part C: counting RGFs by number of values -/

/-- Extend an RGF on `Fin n` by one more value. -/
private def ext {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) : Fin (n+1) → Fin (n+1) :=
  Fin.snoc (fun i => (g i).castSucc) v

private theorem ext_castSucc {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) (j : Fin n) :
    ext g v j.castSucc = (g j).castSucc := by
  simp [ext, Fin.snoc_castSucc]

private theorem ext_last {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) :
    ext g v (Fin.last n) = v := by
  simp [ext, Fin.snoc_last]

private theorem image_ext {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) :
    Finset.univ.image (ext g v) = insert v ((Finset.univ.image g).image Fin.castSucc) := by
  apply Finset.ext
  intro w
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => left; rw [ext_last] at hi; exact hi.symm
    | cast j => right; rw [ext_castSucc] at hi; exact ⟨g j, ⟨j, rfl⟩, hi⟩
  · rintro (hv | ⟨y, ⟨j, hj⟩, hy⟩)
    · exact ⟨Fin.last n, by rw [ext_last]; exact hv.symm⟩
    · exact ⟨j.castSucc, by rw [ext_castSucc, hj, hy]⟩

private theorem card_castImg {n : ℕ} (g : Fin n → Fin n) :
    ((Finset.univ.image g).image Fin.castSucc).card = numVals g := by
  unfold numVals
  rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n)]

private theorem v_mem_castImg {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1)) :
    v ∈ (Finset.univ.image g).image Fin.castSucc ↔ v.val < numVals g := by
  constructor
  · intro hv
    rw [Finset.mem_image] at hv
    obtain ⟨y, hy, hyv⟩ := hv
    have hval : v.val = y.val := by rw [← hyv]; exact Fin.val_castSucc y
    have hy' : y.val < numVals g := (rgf_mem_image hg y).mp hy
    omega
  · intro hlt
    have hvn : v.val < n := lt_of_lt_of_le hlt (numVals_le g)
    rw [Finset.mem_image]
    exact ⟨⟨v.val, hvn⟩, (rgf_mem_image hg ⟨v.val, hvn⟩).mpr hlt, Fin.ext rfl⟩

private theorem numVals_ext_lt {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1))
    (hv : v.val < numVals g) : numVals (ext g v) = numVals g := by
  change (Finset.univ.image (ext g v)).card = numVals g
  rw [image_ext, Finset.insert_eq_self.mpr ((v_mem_castImg hg v).mpr hv)]
  exact card_castImg g

private theorem numVals_ext_eq {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1))
    (hv : v.val = numVals g) : numVals (ext g v) = numVals g + 1 := by
  change (Finset.univ.image (ext g v)).card = numVals g + 1
  rw [image_ext, Finset.card_insert_of_notMem (by rw [v_mem_castImg hg v]; omega), card_castImg g]

private theorem ext_rgf {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1))
    (hv : v.val ≤ numVals g) : IsRGF (ext g v) := by
  intro i j hj
  induction i using Fin.lastCases with
  | last =>
    rw [ext_last] at hj
    have hjn : j.val < n := by
      have := numVals_le g; omega
    have hmem : (⟨j.val, hjn⟩ : Fin n) ∈ Finset.univ.image g :=
      (rgf_mem_image hg ⟨j.val, hjn⟩).mpr (by change j.val < numVals g; omega)
    rw [Finset.mem_image] at hmem
    obtain ⟨a, _, ha⟩ := hmem
    refine ⟨a.castSucc, ?_, ?_⟩
    · rw [Fin.val_castSucc]; exact a.isLt.trans_le (by simp)
    · rw [ext_castSucc, ha]; exact Fin.ext rfl
  | cast b =>
    rw [ext_castSucc] at hj
    have hjn : j.val < n := by
      have := (g b).isLt; rw [Fin.val_castSucc] at hj; omega
    rw [Fin.val_castSucc] at hj
    obtain ⟨a₀, ha₀lt, ha₀⟩ := hg b ⟨j.val, hjn⟩ (by exact hj)
    refine ⟨a₀.castSucc, ?_, ?_⟩
    · rw [Fin.val_castSucc, Fin.val_castSucc]; exact ha₀lt
    · rw [ext_castSucc, ha₀]; exact Fin.ext rfl

/-- Restrict an RGF on `Fin (n+1)` to its first `n` coordinates. -/
private def restr {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) : Fin n → Fin n :=
  fun i => ⟨(f i.castSucc).val, by
    have h := rgf_subdiag hf i.castSucc
    rw [Fin.val_castSucc] at h
    exact lt_of_le_of_lt h i.isLt⟩

private theorem restr_castSucc {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) (i : Fin n) :
    Fin.castSucc (restr f hf i) = f i.castSucc := by
  apply Fin.ext; simp [restr]

private theorem decomp {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) :
    f = ext (restr f hf) (f (Fin.last n)) := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [ext_last]
  | cast j => rw [ext_castSucc, restr_castSucc]

private theorem restr_rgf {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) : IsRGF
    (restr f hf) := by
  intro i j' hj'
  have hj'2 : (j'.castSucc).val < (f i.castSucc).val := by
    rw [Fin.val_castSucc]; exact hj'
  obtain ⟨i₀, hi₀lt, hi₀⟩ := hf i.castSucc j'.castSucc hj'2
  rw [Fin.val_castSucc] at hi₀lt
  refine ⟨⟨i₀.val, lt_trans hi₀lt i.isLt⟩, hi₀lt, ?_⟩
  apply Fin.ext
  show (restr f hf ⟨i₀.val, _⟩).val = j'.val
  have : (⟨i₀.val, lt_trans hi₀lt i.isLt⟩ : Fin n).castSucc = i₀ := Fin.ext (by simp)
  simp only [restr]
  rw [this, hi₀, Fin.val_castSucc]

private theorem restr_ext {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) (hf : IsRGF (ext g v)) :
    restr (ext g v) hf = g := by
  funext i
  apply Fin.ext
  change (ext g v i.castSucc).val = (g i).val
  rw [ext_castSucc, Fin.val_castSucc]

private theorem last_le {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) :
    (f (Fin.last n)).val ≤ numVals (restr f hf) := by
  by_contra hc
  rw [not_le] at hc
  have hbnd : numVals (restr f hf) < n := by
    have := rgf_subdiag hf (Fin.last n)
    simp only [Fin.val_last] at this
    omega
  have hjval : (⟨numVals (restr f hf), by omega⟩ : Fin (n+1)).val < (f (Fin.last n)).val := by
    simpa using hc
  obtain ⟨i₀, _, hi₀⟩ := hf (Fin.last n) ⟨numVals (restr f hf), by omega⟩ hjval
  have hi₀n : i₀.val < n := by
    have := i₀.isLt; omega
  have hmem : (⟨numVals (restr f hf), hbnd⟩ : Fin n) ∈ Finset.univ.image (restr f hf) := by
    rw [Finset.mem_image]
    refine ⟨⟨i₀.val, hi₀n⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change (restr f hf ⟨i₀.val, hi₀n⟩).val = numVals (restr f hf)
    have hcs : (⟨i₀.val, hi₀n⟩ : Fin n).castSucc = i₀ := Fin.ext (by simp)
    simp only [restr]
    rw [hcs, hi₀]
  rw [rgf_mem_image (restr_rgf f hf)] at hmem
  simp at hmem

/-- RGFs on `Fin n` with exactly `K` values. -/
private abbrev Asub (n K : ℕ) := {f : Fin n → Fin n // IsRGF f ∧ numVals f = K}
private abbrev Psub (n K : ℕ) := {p : (Fin n → Fin n) × Fin (n+1) //
  IsRGF p.1 ∧ p.2.val ≤ numVals p.1 ∧ numVals (ext p.1 p.2) = K}

private def E1 (n K : ℕ) : Asub (n+1) K ≃ Psub n K where
  toFun f := ⟨(restr f.1 f.2.1, f.1 (Fin.last n)),
    ⟨restr_rgf f.1 f.2.1, last_le f.1 f.2.1, by rw [← decomp f.1 f.2.1]; exact f.2.2⟩⟩
  invFun p := ⟨ext p.1.1 p.1.2, ⟨ext_rgf p.2.1 p.1.2 p.2.2.1, p.2.2.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    exact (decomp f.1 f.2.1).symm
  right_inv p := by
    obtain ⟨⟨g, v⟩, hp⟩ := p
    apply Subtype.ext
    change (restr (ext g v) (ext_rgf hp.1 v hp.2.1), ext g v (Fin.last n)) = (g, v)
    rw [restr_ext, ext_last]

private def extPair_inl {n k : ℕ} (g : Asub n (k + 1)) (i : Fin (k + 1)) : Psub n (k+1) := by
  have hb : i.val < n + 1 := by
    have := numVals_le g.1; have := g.2.2; have := i.isLt; omega
  have hlt : (⟨i.val, hb⟩ : Fin (n+1)).val < numVals g.1 := by
    change i.val < numVals g.1; have := g.2.2; have := i.isLt; omega
  exact ⟨(g.1, ⟨i.val, hb⟩), g.2.1, le_of_lt hlt, by rw [numVals_ext_lt g.2.1 _ hlt, g.2.2]⟩

private def extPair_inr {n k : ℕ} (g : Asub n k) : Psub n (k+1) := by
  have hb : numVals g.1 < n + 1 := by have := numVals_le g.1; omega
  have heq : (⟨numVals g.1, hb⟩ : Fin (n+1)).val = numVals g.1 := rfl
  exact ⟨(g.1, ⟨numVals g.1, hb⟩), g.2.1, le_of_eq heq, by rw [numVals_ext_eq g.2.1 _ heq, g.2.2]⟩

private def fromSum (n k : ℕ) : ((Asub n (k+1)) × Fin (k+1)) ⊕ Asub n k → Psub n (k+1)
  | Sum.inl (g, i) => extPair_inl g i
  | Sum.inr g => extPair_inr g

private theorem fromSum_bij (n k : ℕ) : Function.Bijective (fromSum n k) := by
  constructor
  · rintro (⟨g, i⟩ | g) (⟨g', i'⟩ | g') hab
    · have hpair : (extPair_inl g i).1 = (extPair_inl g' i').1 := congrArg Subtype.val hab
      simp only [extPair_inl] at hpair
      rw [Prod.mk.injEq] at hpair
      have hg : g = g' := Subtype.ext hpair.1
      subst hg
      have hi : i = i' := Fin.ext (by have := congrArg Fin.val hpair.2; simpa using this)
      subst hi; rfl
    · exfalso
      have hpair : (extPair_inl g i).1 = (extPair_inr g').1 := congrArg Subtype.val hab
      simp only [extPair_inl, extPair_inr] at hpair
      rw [Prod.mk.injEq] at hpair
      have e := congrArg numVals hpair.1
      rw [g.2.2, g'.2.2] at e; omega
    · exfalso
      have hpair : (extPair_inr g).1 = (extPair_inl g' i').1 := congrArg Subtype.val hab
      simp only [extPair_inl, extPair_inr] at hpair
      rw [Prod.mk.injEq] at hpair
      have e := congrArg numVals hpair.1
      rw [g.2.2, g'.2.2] at e; omega
    · have hpair : (extPair_inr g).1 = (extPair_inr g').1 := congrArg Subtype.val hab
      simp only [extPair_inr] at hpair
      rw [Prod.mk.injEq] at hpair
      have hg : g = g' := Subtype.ext hpair.1
      subst hg; rfl
  · rintro ⟨⟨g, v⟩, hr, hle, heqk⟩
    have heqk' : numVals (ext g v) = k + 1 := heqk
    by_cases h : v.val < numVals g
    · have hgk : numVals g = k + 1 := (numVals_ext_lt hr v h).symm.trans heqk'
      have hvk : v.val < k + 1 := by omega
      refine ⟨Sum.inl (⟨g, hr, hgk⟩, ⟨v.val, hvk⟩), ?_⟩
      apply Subtype.ext
      simp only [fromSum, extPair_inl]
    · have heq : v.val = numVals g := le_antisymm hle (not_lt.mp h)
      have hgk : numVals g = k := by
        have h2 : numVals (ext g v) = numVals g + 1 := numVals_ext_eq hr v heq
        omega
      refine ⟨Sum.inr ⟨g, hr, hgk⟩, ?_⟩
      apply Subtype.ext
      simp only [fromSum, extPair_inr]
      exact Prod.ext_iff.mpr ⟨rfl, Fin.ext heq.symm⟩

private theorem card_rec (n k : ℕ) :
    Nat.card (Asub (n+1) (k+1)) = (k+1) * Nat.card (Asub n (k+1)) + Nat.card (Asub n k) := by
  have e1 : Nat.card (Asub (n+1) (k+1)) = Nat.card (Psub n (k+1)) := Nat.card_congr (E1 n (k+1))
  have e2 : Nat.card (Psub n (k+1)) = Nat.card (((Asub n (k+1)) × Fin (k+1)) ⊕ Asub n k) :=
    (Nat.card_congr (Equiv.ofBijective _ (fromSum_bij n k))).symm
  rw [e1, e2, Nat.card_sum, Nat.card_prod]
  have hfin : Nat.card (Fin (k+1)) = k + 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hfin]; ring

private theorem card_A_0_0 : Nat.card (Asub 0 0) = 1 := by
  have : Unique (Asub 0 0) :=
    { default := ⟨Fin.elim0, fun i => i.elim0, by simp [numVals]⟩
      uniq := fun a => Subtype.ext (funext (fun i => i.elim0)) }
  exact Nat.card_unique

private theorem card_A_0_succ (k : ℕ) : Nat.card (Asub 0 (k+1)) = 0 := by
  have : IsEmpty (Asub 0 (k+1)) :=
    ⟨fun p => by obtain ⟨f, _, hn⟩ := p; have := numVals_le f; omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private theorem card_A_succ_0 (n : ℕ) : Nat.card (Asub (n+1) 0) = 0 := by
  have : IsEmpty (Asub (n+1) 0) :=
    ⟨fun p => by
      obtain ⟨f, _, hn⟩ := p
      have hne : (Finset.univ.image f).Nonempty :=
        ⟨f ⟨0, Nat.succ_pos n⟩, Finset.mem_image_of_mem f (Finset.mem_univ _)⟩
      have := Finset.Nonempty.card_pos hne
      simp only [numVals] at hn
      omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private theorem rgf_count (n k : ℕ) : Nat.card (Asub n k) = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [card_A_0_0, Nat.stirlingSecond_zero]
    | succ k => rw [card_A_0_succ, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases k with
    | zero => rw [card_A_succ_0, Nat.stirlingSecond_succ_zero]
    | succ k => rw [card_rec, ih (k+1), ih k, Nat.stirlingSecond_succ_succ]

/-! ## Gluing the three parts -/

private theorem bellPerm_inj {n : ℕ} :
    Function.Injective (fun f : {g : Fin n → Fin n // IsRGF g} => bellPerm f.val) := by
  intro a b hab
  exact Subtype.ext (bellPerm_inj_subdiag (rgf_subdiag a.2) (rgf_subdiag b.2) hab)

private theorem main (n k : ℕ) (_hn : 0 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ∃ f : Fin n → Fin n, IsRGF f ∧ bellPerm f = σ ∧ numWeak σ = k} =
      Nat.stirlingSecond n k := by
  rw [← rgf_count n k]
  refine (Nat.card_eq_of_bijective (f := fun p : {f : Fin n → Fin n // IsRGF f ∧ numVals f = k} =>
    (⟨bellPerm p.val, ⟨p.val, p.2.1, rfl, by rw [numWeak_bellPerm p.2.1, p.2.2]⟩⟩ :
      {σ : Equiv.Perm (Fin n) // ∃ f : Fin n → Fin n, IsRGF f ∧ bellPerm f = σ ∧ numWeak σ = k}))
          ?_).symm
  constructor
  · intro a b hab
    simp only [Subtype.mk.injEq] at hab
    have h1 : bellPerm a.val = bellPerm b.val := hab
    have h2 := @bellPerm_inj n ⟨a.val, a.2.1⟩ ⟨b.val, b.2.1⟩ h1
    have h3 : a.val = b.val := by simpa using congrArg (·.val) h2
    exact Subtype.ext h3
  · rintro ⟨σ, f, hrgf, hbp, hweak⟩
    refine ⟨⟨f, hrgf, ?_⟩, ?_⟩
    · rw [← numWeak_bellPerm hrgf, hbp, hweak]
    · apply Subtype.ext; exact hbp

/--
**Weak excedances of Bell permutations of the second kind.** Let $n \ge 1$ and $k$ be natural
numbers, and write $[n] = \{0, \dots, n-1\}$. A function $f : [n] \to [n]$ is a restricted
growth function if for every $i$, every $j < f(i)$ equals $f(i_0)$ for some $i_0 < i$. Its Bell
permutation is the product of transpositions $(0\ f(0))(1\ f(1)) \cdots (n-1\ f(n-1))$, composed
so that the rightmost factor acts first, where $(i\ i)$ denotes the identity. A weak excedance
of a permutation $\sigma$ of $[n]$ is an index $i$ with $i \le \sigma(i)$. Then the number of
permutations of $[n]$ that are the Bell permutation of some restricted growth function and have
exactly $k$ weak excedances is the Stirling number of the second kind $S(n, k)$.

Proves `Wanted` entry `bell_perm_second_kind_weakExcedance_eq_stirlingSecond`.

Source: Fufa Beyene, Jörgen Backelin, Roberto Mantaci, and Samuel A. Fufa,
"Set Partitions and Other Bell Number Enumerated Objects," Journal of Integer
Sequences 26 (2023), Article 23.1.8, Corollary (label corcycfx), item 1,
lines 283–290,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Beyene/beyene13.tex
-/
theorem bell_perm_second_kind_weakExcedance_eq_stirlingSecond
    (n k : ℕ) (hn : 0 < n) :
    let IsRGF : (Fin n → Fin n) → Prop :=
      fun f => ∀ i : Fin n, ∀ j : Fin n, j.val < (f i).val →
        ∃ i₀ : Fin n, i₀.val < i.val ∧ f i₀ = j;
    let bellPerm : (Fin n → Fin n) → Equiv.Perm (Fin n) :=
      fun f => ((List.finRange n).map fun i => Equiv.swap i (f i)).prod;
    let numWeak : Equiv.Perm (Fin n) → ℕ :=
      fun σ => Fintype.card {i : Fin n // i ≤ σ i};
    Nat.card {σ : Equiv.Perm (Fin n) //
      ∃ f : Fin n → Fin n, IsRGF f ∧ bellPerm f = σ ∧ numWeak σ = k} =
      Nat.stirlingSecond n k := by
  exact main n k hn

end MetaMathlibExt
