/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin

@[expose] public section

section
namespace MetaMathlibExt

/-- Descent indicator at position `n`: `1` if `w n > w (n+1)`, else `0`. -/
private def desInd {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) : ℕ :=
  if h : n + 1 < K then
    if w ⟨n, by omega⟩ > w ⟨n + 1, h⟩ then 1 else 0
  else 0

/-- Prefix descent count: descents of `w` strictly before position `n`. -/
private def desPrefix {m K : ℕ} (w : Fin K → Fin m) : ℕ → ℕ
  | 0 => 0
  | n + 1 => desPrefix w n + desInd w n

private theorem desPrefix_zero {m K : ℕ} (w : Fin K → Fin m) :
    desPrefix w 0 = 0 :=
  rfl

private theorem desPrefix_succ {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
    desPrefix w (n + 1) = desPrefix w n + desInd w n :=
  rfl

private theorem desInd_le_one {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
    desInd w n ≤ 1 := by
  unfold desInd
  by_cases hn : n + 1 < K
  · simp only [hn, dite_true]
    by_cases hw : w ⟨n, by omega⟩ > w ⟨n + 1, hn⟩
    · simp only [hw, ite_true]
      omega
    · simp only [hw, ite_false]
      omega
  · simp only [hn, dite_false]
    omega

private theorem desPrefix_le_succ {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
    desPrefix w n ≤ desPrefix w (n + 1) := by
  rw [desPrefix_succ]
  exact Nat.le_add_right _ _

private theorem desPrefix_mono {m K : ℕ} (w : Fin K → Fin m) :
    Monotone (desPrefix w) :=
  monotone_nat_of_le_succ (desPrefix_le_succ w)

private theorem desPrefix_le_self {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
    desPrefix w n ≤ n := by
  induction n with
  | zero =>
    rw [desPrefix_zero]
  | succ n ih =>
    rw [desPrefix_succ]
    have h1 := desInd_le_one w n
    omega

private theorem desInd_eq_zero_of_ge {m K : ℕ} (w : Fin K → Fin m)
    (n : ℕ) (h : ¬ n + 1 < K) : desInd w n = 0 := by
  unfold desInd
  simp only [h, dite_false]

private theorem desPrefix_le_total {m K : ℕ} (w : Fin K → Fin m)
    (n : ℕ) (h : n ≤ K) : desPrefix w n ≤ desPrefix w K :=
  (desPrefix_mono w) h

/-- Weakly increasing with strict increases at descents of `w`. -/
private def IsMono {m K x : ℕ} (w : Fin K → Fin m)
    (e : Fin K → Fin x) : Prop :=
  Monotone e ∧
    ∀ (j : Fin K) (h : j.val + 1 < K),
      w j > w ⟨j.val + 1, h⟩ → e j < e ⟨j.val + 1, h⟩

private noncomputable instance decIsMono {m K x : ℕ}
    (w : Fin K → Fin m) :
    DecidablePred (IsMono (x := x) w) :=
  fun e => Classical.propDecidable (IsMono w e)

private theorem mono_gap {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (b : ℕ)
    (hb : b + 1 < K) :
    (e ⟨b, by omega⟩).val + desInd w b ≤
      (e ⟨b + 1, hb⟩).val := by
  have hdes : desInd w b =
      (if w ⟨b, by omega⟩ > w ⟨b + 1, hb⟩ then 1 else 0) := by
    unfold desInd
    simp only [hb, dite_true]
  rw [hdes]
  by_cases hw : w ⟨b, by omega⟩ > w ⟨b + 1, hb⟩
  · simp only [hw, ite_true]
    have hlt : e ⟨b, by omega⟩ < e ⟨b + 1, hb⟩ :=
      hmono.2 ⟨b, by omega⟩ hb hw
    have hval :
        (e ⟨b, by omega⟩).val < (e ⟨b + 1, hb⟩).val :=
      Fin.lt_def.mp hlt
    omega
  · simp only [hw, ite_false]
    have hle : (⟨b, by omega⟩ : Fin K) ≤ ⟨b + 1, hb⟩ := by
      change b ≤ b + 1
      omega
    have hle_e : e ⟨b, by omega⟩ ≤ e ⟨b + 1, hb⟩ :=
      hmono.1 hle
    have hval :
        (e ⟨b, by omega⟩).val ≤ (e ⟨b + 1, hb⟩).val :=
      Fin.le_iff_val_le_val.mp hle_e
    omega

private theorem mono_lower {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (n : ℕ)
    (hn : n < K) : desPrefix w n ≤ (e ⟨n, hn⟩).val := by
  induction n with
  | zero =>
    rw [desPrefix_zero]
    omega
  | succ n ih =>
    have hn' : n < K := by omega
    have hih := ih hn'
    have hgap := mono_gap hmono n hn
    have heq : (e ⟨n, hn'⟩).val = (e ⟨n, by omega⟩).val := rfl
    rw [desPrefix_succ]
    omega

private theorem desPrefix_last {m K : ℕ} (w : Fin K → Fin m)
    (hK : 0 < K) : desPrefix w K = desPrefix w (K - 1) := by
  have hK1 : K - 1 + 1 = K := by omega
  have hKK : K = K - 1 + 1 := hK1.symm
  have h1 : desPrefix w K = desPrefix w (K - 1 + 1) :=
    congrArg (desPrefix w) hKK
  rw [h1, desPrefix_succ]
  have h0 : desInd w (K - 1) = 0 := by
    apply desInd_eq_zero_of_ge
    omega
  rw [h0, Nat.add_zero]

private theorem mono_leap {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (a b : ℕ)
    (hab : a ≤ b) (hb : b < K) (ha : a < K) :
    (e ⟨a, ha⟩).val + (desPrefix w b - desPrefix w a) ≤
      (e ⟨b, hb⟩).val := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp only [Nat.sub_self, Nat.add_zero]
    exact Nat.le_refl _
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq
      simp only [Nat.sub_self, Nat.add_zero]
      exact Nat.le_refl _
    · have hab' : a ≤ b := by omega
      have hb' : b < K := by omega
      have hih := ih hab' hb'
      have hgap := mono_gap hmono b hb
      have hle : desPrefix w a ≤ desPrefix w b :=
        (desPrefix_mono w) hab'
      have hsucc : desPrefix w (b + 1) =
          desPrefix w b + desInd w b :=
        desPrefix_succ w b
      have heq_b : (e ⟨b, hb'⟩).val =
          (e ⟨b, by omega⟩).val := rfl
      omega

private theorem mono_upper {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (n : ℕ)
    (hn : n < K) :
    (e ⟨n, hn⟩).val + (desPrefix w K - desPrefix w n) < x := by
  have hK : 0 < K := by omega
  have hle_n : n ≤ K - 1 := by omega
  have hb : K - 1 < K := by omega
  have hleap := mono_leap hmono n (K - 1) hle_n hb hn
  have hlast : desPrefix w K = desPrefix w (K - 1) :=
    desPrefix_last w hK
  have hlt : (e ⟨K - 1, hb⟩).val < x := (e ⟨K - 1, hb⟩).isLt
  omega

/-- Forward shift: subtract prefix descents from a monotone map. -/
private def shiftFwd {m K x : ℕ} (w : Fin K → Fin m)
    (e : Fin K → Fin x) (hmono : IsMono w e) :
    Fin K → Fin (x - desPrefix w K) :=
  fun j =>
    have h1 : desPrefix w j.val ≤ (e j).val :=
      mono_lower hmono j.val j.isLt
    have h2 : (e j).val +
        (desPrefix w K - desPrefix w j.val) < x :=
      mono_upper hmono j.val j.isLt
    have h3 : desPrefix w j.val ≤ desPrefix w K :=
      desPrefix_le_total w j.val (by omega)
    ⟨(e j).val - desPrefix w j.val, by omega⟩

/-- Backward shift: add prefix descents to a monotone map. -/
private def shiftBwd {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) :
    Fin K → Fin x :=
  fun j =>
    if hle : desPrefix w K ≤ x then
      have h1 : (g j).val < x - desPrefix w K := (g j).isLt
      have h2 : desPrefix w j.val ≤ desPrefix w K :=
        desPrefix_le_total w j.val (by omega)
      ⟨(g j).val + desPrefix w j.val, by omega⟩
    else
      have hx : x ≤ desPrefix w K := by omega
      have h0 : x - desPrefix w K = 0 :=
        Nat.sub_eq_zero_of_le hx
      Fin.elim0 (h0 ▸ g j)

private theorem shiftFwd_mono {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} {hmono : IsMono w e} :
    Monotone (shiftFwd w e hmono) := by
  intro a b hab
  have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
  have ha' : a.val < K := a.isLt
  have hb' : b.val < K := b.isLt
  have hleap := mono_leap hmono a.val b.val hab' hb' ha'
  have hlow_a : desPrefix w a.val ≤ (e a).val :=
    mono_lower hmono a.val ha'
  have hlow_b : desPrefix w b.val ≤ (e b).val :=
    mono_lower hmono b.val hb'
  have hle_s : desPrefix w a.val ≤ desPrefix w b.val :=
    (desPrefix_mono w) hab'
  have heq_a : (e ⟨a.val, ha'⟩).val = (e a).val := rfl
  have heq_b : (e ⟨b.val, hb'⟩).val = (e b).val := rfl
  rw [Fin.le_iff_val_le_val]
  change (e a).val - desPrefix w a.val ≤
    (e b).val - desPrefix w b.val
  omega

private theorem shiftBwd_monotone {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g) :
    Monotone (shiftBwd w g) := by
  intro a b hab
  by_cases hle : desPrefix w K ≤ x
  · have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
    have hg_le : g a ≤ g b := hg hab
    have hg_val : (g a).val ≤ (g b).val :=
      Fin.le_iff_val_le_val.mp hg_le
    have hs_le : desPrefix w a.val ≤ desPrefix w b.val :=
      (desPrefix_mono w) hab'
    unfold shiftBwd
    simp only [hle, dite_true]
    rw [Fin.le_iff_val_le_val]
    change (g a).val + desPrefix w a.val ≤
      (g b).val + desPrefix w b.val
    omega
  · have hx : x ≤ desPrefix w K := by omega
    have h0 : x - desPrefix w K = 0 :=
      Nat.sub_eq_zero_of_le hx
    have hfalse : False := Fin.elim0 (h0 ▸ g a)
    exact False.elim hfalse

private theorem shiftBwd_strict {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g)
    (j : Fin K) (h : j.val + 1 < K)
    (hw : w j > w ⟨j.val + 1, h⟩) :
    shiftBwd w g j < shiftBwd w g ⟨j.val + 1, h⟩ := by
  by_cases hle : desPrefix w K ≤ x
  · have hj_le : j ≤ ⟨j.val + 1, h⟩ := by
      change j.val ≤ j.val + 1
      omega
    have hg_le : g j ≤ g ⟨j.val + 1, h⟩ := hg hj_le
    have hg_val : (g j).val ≤ (g ⟨j.val + 1, h⟩).val :=
      Fin.le_iff_val_le_val.mp hg_le
    have hw' : w ⟨j.val, by omega⟩ > w ⟨j.val + 1, h⟩ := hw
    have hdes1 : desInd w j.val = 1 := by
      unfold desInd
      simp only [h, dite_true, hw', ite_true]
    have hsucc : desPrefix w (j.val + 1) =
        desPrefix w j.val + 1 := by
      rw [desPrefix_succ, hdes1]
    unfold shiftBwd
    simp only [hle, dite_true]
    rw [Fin.lt_def]
    change (g j).val + desPrefix w j.val <
      (g ⟨j.val + 1, h⟩).val + desPrefix w (j.val + 1)
    omega
  · have hx : x ≤ desPrefix w K := by omega
    have h0 : x - desPrefix w K = 0 :=
      Nat.sub_eq_zero_of_le hx
    have hfalse : False := Fin.elim0 (h0 ▸ g j)
    exact False.elim hfalse

private theorem mono_des_le {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) :
    desPrefix w K ≤ x := by
  by_cases hK : K = 0
  · subst hK
    rw [desPrefix_zero]
    exact Nat.zero_le _
  · have hKpos : 0 < K := by omega
    have hup := mono_upper hmono 0 hKpos
    have hz : desPrefix w 0 = 0 := desPrefix_zero w
    omega

private theorem shiftBwd_isMono {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g) :
    IsMono w (shiftBwd w g) := by
  constructor
  · exact shiftBwd_monotone w g hg
  · intro j h hw
    exact shiftBwd_strict w g hg j h hw

private theorem shiftFwdBwd {m K x : ℕ} (w : Fin K → Fin m)
    (e : Fin K → Fin x) (hmono : IsMono w e) :
    shiftBwd w (shiftFwd w e hmono) = e := by
  have hle : desPrefix w K ≤ x := mono_des_le hmono
  funext j
  have hn : j.val < K := j.isLt
  have hlow : desPrefix w j.val ≤ (e j).val :=
    mono_lower hmono j.val hn
  have hg_val : ((shiftFwd w e hmono) j).val =
      (e j).val - desPrefix w j.val := rfl
  have h1g : ((shiftFwd w e hmono) j).val <
      x - desPrefix w K :=
    ((shiftFwd w e hmono) j).isLt
  have h2s : desPrefix w j.val ≤ desPrefix w K :=
    desPrefix_le_total w j.val (by omega)
  have he_eq : shiftBwd w (shiftFwd w e hmono) j =
      ⟨((shiftFwd w e hmono) j).val + desPrefix w j.val,
        by omega⟩ := by
    unfold shiftBwd
    simp only [hle, dite_true]
  apply Fin.ext
  simp only [he_eq, hg_val]
  exact Nat.sub_add_cancel hlow

private theorem shiftBwdFwd {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g) :
    shiftFwd w (shiftBwd w g)
        (shiftBwd_isMono w g hg) = g := by
  by_cases hle : desPrefix w K ≤ x
  · funext j
    have he_val : ((shiftBwd w g) j).val =
        (g j).val + desPrefix w j.val := by
      unfold shiftBwd
      simp only [hle, dite_true]
    have hg_val : ((shiftFwd w (shiftBwd w g)
        (shiftBwd_isMono w g hg)) j).val =
        ((shiftBwd w g) j).val - desPrefix w j.val := rfl
    apply Fin.ext
    simp only [hg_val, he_val]
    exact Nat.add_sub_cancel _ _
  · have hx : x ≤ desPrefix w K := by omega
    have h0 : x - desPrefix w K = 0 :=
      Nat.sub_eq_zero_of_le hx
    funext j
    have hfalse : False := Fin.elim0 (h0 ▸ g j)
    exact False.elim hfalse

private noncomputable instance decMonotone {K y : ℕ} :
    DecidablePred (Monotone : (Fin K → Fin y) → Prop) :=
  fun g => Classical.propDecidable (Monotone g)

private def shiftEquiv {m K x : ℕ} (w : Fin K → Fin m) :
    { e : Fin K → Fin x // IsMono w e } ≃
      { g : Fin K → Fin (x - desPrefix w K) // Monotone g } where
  toFun := fun ⟨e, hmono⟩ => ⟨shiftFwd w e hmono, shiftFwd_mono⟩
  invFun := fun ⟨g, hg⟩ => ⟨shiftBwd w g, shiftBwd_isMono w g hg⟩
  left_inv := fun ⟨e, hmono⟩ =>
    Subtype.ext (shiftFwdBwd w e hmono)
  right_inv := fun ⟨g, hg⟩ =>
    Subtype.ext (shiftBwdFwd w g hg)

/-- The left-hand side counts tuples of multisets, by `Sym.card_sym_eq_choose`. -/
private theorem worpitzky_lhs_card (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
    Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
      Fintype.card (∀ i, Sym (Fin x) (k i)) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]

/-- Multiset of a tuple, via `List.ofFn`. -/
private def monoToSym {α : Type*} [LinearOrder α] {K : ℕ}
    (f : Fin K → α) : Sym α K :=
  ⟨↑(List.ofFn f), by rw [Multiset.coe_card, List.length_ofFn]⟩

/-- Sorted list of a multiset has length `K`. -/
private theorem symSortLength {α : Type*} [LinearOrder α] {K : ℕ}
    (S : Sym α K) : (S.val.sort (· ≤ ·)).length = K := by
  rw [Multiset.length_sort, S.2]

/-- Monotone enumeration of a multiset, via sorted list. -/
private def symToMono {α : Type*} [LinearOrder α] {K : ℕ}
    (S : Sym α K) : Fin K → α :=
  fun j => (S.val.sort (· ≤ ·)).get
    (Fin.cast (symSortLength S).symm j)

/-- Sorted enumeration is monotone. -/
private theorem symToMono_mono {α : Type*} [LinearOrder α] {K : ℕ}
    (S : Sym α K) : Monotone (symToMono S) := by
  have hsort : (S.val.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort _ _
  have hmono : Monotone (S.val.sort (· ≤ ·)).get :=
    hsort.sortedLE.monotone_get
  intro a b hab
  have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
  have hcast : Fin.cast (symSortLength S).symm a ≤
      Fin.cast (symSortLength S).symm b := by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_cast]
    exact hab'
  exact hmono hcast

/-- Sorting a sorted tuple is identity. -/
private theorem sort_ofFn_eq {α : Type*} [LinearOrder α] {K : ℕ}
    (f : Fin K → α) (hf : Monotone f) :
    ((↑(List.ofFn f) : Multiset α).sort (· ≤ ·)) = List.ofFn f := by
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hf.sortedLE_ofFn.pairwise

private theorem wmi_monoToSym_symToMono {α : Type*} [LinearOrder α] {K : ℕ}
    (S : Sym α K) : monoToSym (symToMono S) = S := by
  apply Sym.ext
  change (↑(List.ofFn (symToMono S)) : Multiset α) = S.val
  have hlist : List.ofFn (symToMono S) = S.val.sort (· ≤ ·) := by
    change List.ofFn (fun j => (S.val.sort (· ≤ ·)).get
      (Fin.cast (symSortLength S).symm j)) = S.val.sort (· ≤ ·)
    simpa only [List.ofFn_get] using
      (List.ofFn_congr (symSortLength S) (S.val.sort (· ≤ ·)).get).symm
  rw [hlist, Multiset.sort_eq]

private theorem wmi_monoToSym_injective {α : Type*} [LinearOrder α] {K : ℕ} :
    Function.Injective
      (fun f : { f : Fin K → α // Monotone f } => monoToSym f.1) := by
  intro f g hfg
  apply Subtype.ext
  apply List.ofFn_injective
  have hvals : (monoToSym f.1).val = (monoToSym g.1).val :=
    congrArg (fun S : Sym α K => S.val) hfg
  change (↑(List.ofFn (f : Fin K → α)) : Multiset α) =
    ↑(List.ofFn (g : Fin K → α)) at hvals
  have hsorted := congrArg (fun s : Multiset α => s.sort (· ≤ ·)) hvals
  rw [sort_ofFn_eq (f := (f : Fin K → α)) f.2,
    sort_ofFn_eq (f := (g : Fin K → α)) g.2] at hsorted
  exact hsorted

/-- Monotone tuples are the sorted enumerations of multisets. -/
private def wmiMonoEquivSym {α : Type*} [LinearOrder α] {K : ℕ} :
    { f : Fin K → α // Monotone f } ≃ Sym α K where
  toFun f := monoToSym f
  invFun S := ⟨symToMono S, symToMono_mono S⟩
  left_inv f := by
    apply wmi_monoToSym_injective
    exact wmi_monoToSym_symToMono (monoToSym (f : Fin K → α))
  right_inv := wmi_monoToSym_symToMono

private theorem wmi_card_monotone (K y : ℕ) :
    Fintype.card { g : Fin K → Fin y // Monotone g } =
      Nat.choose (y + K - 1) K := by
  rw [Fintype.card_congr wmiMonoEquivSym, Sym.card_sym_eq_choose,
    Fintype.card_fin]

private theorem wmi_desPrefix_eq_sum_range {m K : ℕ} (w : Fin K → Fin m)
    (n : ℕ) :
    desPrefix w n = ∑ j ∈ Finset.range n, desInd w j := by
  induction n with
  | zero => simp [desPrefix_zero]
  | succ n ih => simp [desPrefix_succ, Finset.sum_range_succ, ih]

private theorem wmi_desInd_eq_ite {m K : ℕ} (w : Fin K → Fin m)
    (j : Fin K) :
    desInd w j.val =
      if (∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩) then 1 else 0 := by
  unfold desInd
  by_cases h : j.val + 1 < K
  · simp only [h, dite_true]
    have hj : (⟨j.val, by omega⟩ : Fin K) = j := Fin.ext rfl
    rw [hj]
    by_cases hd : w j > w ⟨j.val + 1, h⟩
    · simp [hd]
    · simp [hd]
  · simp [h]

private theorem wmi_desPrefix_eq_card {m K : ℕ} (w : Fin K → Fin m) :
    desPrefix w K =
      (Finset.univ.filter (fun j : Fin K =>
        ∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩)).card := by
  rw [wmi_desPrefix_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range (fun j => desInd w j) K]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact wmi_desInd_eq_ite w j

private theorem wmi_card_isMono_prefix {m K x : ℕ} (w : Fin K → Fin m) :
    Fintype.card { e : Fin K → Fin x // IsMono w e } =
      Nat.choose (x + K - (desPrefix w K + 1)) K := by
  rw [Fintype.card_congr (shiftEquiv w), wmi_card_monotone]
  by_cases hK : K = 0
  · subst K
    simp [desPrefix_zero]
  · by_cases hdx : desPrefix w K ≤ x
    · congr 1
      omega
    · have hleft : x - desPrefix w K + K - 1 < K := by omega
      have hright : x + K - (desPrefix w K + 1) < K := by omega
      rw [Nat.choose_eq_zero_of_lt hleft, Nat.choose_eq_zero_of_lt hright]

private theorem wmi_card_isMono {m K x : ℕ} (w : Fin K → Fin m) :
    Fintype.card { e : Fin K → Fin x // IsMono w e } =
      Nat.choose
        (x + K - ((Finset.univ.filter (fun j : Fin K =>
          ∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩)).card + 1)) K := by
  rw [← wmi_desPrefix_eq_card w]
  exact wmi_card_isMono_prefix w

private theorem wmi_pair_monotone_iff {m K x : ℕ}
    (w : Fin K → Fin m) (e : Fin K → Fin x) :
    Monotone (fun j => (toLex (e j, w j) : Fin x ×ₗ Fin m)) ↔ IsMono w e := by
  constructor
  · intro h
    constructor
    · intro a b hab
      rcases Prod.Lex.toLex_le_toLex.mp (h hab) with he | ⟨he, -⟩
      · exact he.le
      · exact he.le
    · intro j hj hw
      have hidx : j ≤ (⟨j.val + 1, hj⟩ : Fin K) := by
        change j.val ≤ j.val + 1
        omega
      rcases Prod.Lex.toLex_le_toLex.mp (h hidx) with he | ⟨-, hword⟩
      · exact he
      · exact False.elim (not_le_of_gt hw hword)
  · intro h
    cases K with
    | zero =>
        intro a
        exact Fin.elim0 a
    | succ n =>
        rw [Fin.monotone_iff_le_succ]
        intro j
        have hidx : j.castSucc ≤ j.succ := by
          rw [Fin.le_iff_val_le_val]
          simp
        have he := h.1 hidx
        apply Prod.Lex.toLex_le_toLex.mpr
        by_cases heq : e j.castSucc = e j.succ
        · right
          refine ⟨heq, ?_⟩
          by_contra hword
          have hgt : w j.castSucc > w j.succ := lt_of_not_ge hword
          have hstrict : e j.castSucc < e j.succ := by
            have hbound : (j.castSucc).val + 1 < n + 1 := by simp
            have hnext : (⟨(j.castSucc).val + 1, hbound⟩ : Fin (n + 1)) = j.succ :=
              Fin.ext (by simp)
            have hgt' : w j.castSucc > w ⟨(j.castSucc).val + 1, hbound⟩ := by
              rw [hnext]
              exact hgt
            have hs := h.2 j.castSucc hbound hgt'
            rw [hnext] at hs
            exact hs
          exact (ne_of_lt hstrict) heq
        · exact Or.inl (lt_of_le_of_ne he heq)

private abbrev wmiWordData (m K x : ℕ) (k : Fin m → ℕ) :=
  Σ w : { w : Fin K → Fin m //
      ∀ i, Fintype.card { j : Fin K // w j = i } = k i },
    { e : Fin K → Fin x // IsMono w.1 e }

private abbrev wmiPairData (m K x : ℕ) (k : Fin m → ℕ) :=
  { f : Fin K → (Fin x ×ₗ Fin m) //
    Monotone f ∧
      ∀ i, Fintype.card { j : Fin K // (ofLex (f j)).2 = i } = k i }

private def wmiWordPairEquiv (m K x : ℕ) (k : Fin m → ℕ) :
    wmiWordData m K x k ≃ wmiPairData m K x k where
  toFun z :=
    ⟨fun j => toLex (z.2.1 j, z.1.1 j),
      (wmi_pair_monotone_iff z.1.1 z.2.1).2 z.2.2,
      fun i => by
        calc
          Fintype.card { j : Fin K //
              (ofLex (toLex (z.2.1 j, z.1.1 j))).2 = i } =
              Fintype.card { j : Fin K // z.1.1 j = i } := by
                apply Fintype.card_congr
                apply Equiv.subtypeEquivRight
                intro j
                simp
          _ = k i := z.1.2 i⟩
  invFun f :=
    ⟨⟨fun j => (ofLex (f.1 j)).2, f.2.2⟩,
      ⟨fun j => (ofLex (f.1 j)).1,
        (wmi_pair_monotone_iff _ _).1 f.2.1⟩⟩
  left_inv z := by
    rcases z with ⟨⟨w, hw⟩, ⟨e, he⟩⟩
    rfl
  right_inv f := by
    apply Subtype.ext
    funext j
    simp

private theorem wmi_card_filter_ofFn {α : Type*} {K : ℕ}
    (f : Fin K → α) (p : α → Prop) [DecidablePred p] :
    ((↑(List.ofFn f) : Multiset α).filter p).card =
      Fintype.card { j : Fin K // p (f j) } := by
  classical
  rw [Fintype.card_subtype]
  induction K with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      change (Multiset.filter p
        (f 0 ::ₘ (↑(List.ofFn fun j : Fin n => f j.succ) : Multiset α))).card = _
      rw [Multiset.filter_cons, Fin.card_filter_univ_succ]
      by_cases h : p (f 0)
      · rw [ite_eq_left h, ite_eq_left h, Multiset.card_add, Multiset.card_singleton,
          ih (fun j => f j.succ)]
        omega
      · rw [ite_eq_right h, ite_eq_right h, zero_add, ih (fun j => f j.succ)]

private abbrev wmiPairMonoData (m K x : ℕ) (k : Fin m → ℕ) :=
  { f : { f : Fin K → (Fin x ×ₗ Fin m) // Monotone f } //
    ∀ i, Fintype.card { j : Fin K // (ofLex (f.1 j)).2 = i } = k i }

private def wmiPairDataNestEquiv (m K x : ℕ) (k : Fin m → ℕ) :
    wmiPairData m K x k ≃ wmiPairMonoData m K x k where
  toFun f := ⟨⟨f.1, f.2.1⟩, f.2.2⟩
  invFun f := ⟨f.1.1, f.1.2, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem wmi_content_iff_filter {m K x : ℕ} (k : Fin m → ℕ)
    (f : Fin K → (Fin x ×ₗ Fin m)) :
    (∀ i, Fintype.card { j : Fin K // (ofLex (f j)).2 = i } = k i) ↔
      ∀ i, ((monoToSym f).val.filter
        (fun q => (ofLex q).2 = i)).card = k i := by
  constructor
  · intro h i
    change ((↑(List.ofFn f) : Multiset (Fin x ×ₗ Fin m)).filter
      (fun q => (ofLex q).2 = i)).card = k i
    exact (wmi_card_filter_ofFn f (fun q => (ofLex q).2 = i)).trans (h i)
  · intro h i
    rw [← wmi_card_filter_ofFn f (fun q => (ofLex q).2 = i)]
    exact h i

private abbrev wmiPairSymData (m K x : ℕ) (k : Fin m → ℕ) :=
  { S : Sym (Fin x ×ₗ Fin m) K //
    ∀ i, (S.val.filter (fun q => (ofLex q).2 = i)).card = k i }

private def wmiPairMonoSymEquiv (m K x : ℕ) (k : Fin m → ℕ) :
    wmiPairMonoData m K x k ≃ wmiPairSymData m K x k :=
  Equiv.subtypeEquiv
    (wmiMonoEquivSym (α := Fin x ×ₗ Fin m) (K := K)) fun f => by
      change (∀ i, Fintype.card { j : Fin K // (ofLex (f.1 j)).2 = i } = k i) ↔
        ∀ i, ((monoToSym f.1).val.filter
          (fun q => (ofLex q).2 = i)).card = k i
      exact wmi_content_iff_filter k f.1

private def wmiPairSymEquiv (m K x : ℕ) (k : Fin m → ℕ) :
    wmiPairData m K x k ≃ wmiPairSymData m K x k :=
  (wmiPairDataNestEquiv m K x k).trans (wmiPairMonoSymEquiv m K x k)

private theorem wmi_sum_filter_fibers {ι α : Type*} [Fintype ι]
    [DecidableEq ι] (s : Multiset α) (c : α → ι) :
    (∑ i, s.filter (fun a => c a = i)) = s := by
  classical
  apply Multiset.ext.mpr
  intro a
  rw [Multiset.count_sum']
  simp only [Multiset.count_filter]
  simp

private def wmiPack {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) : Multiset (Fin x ×ₗ Fin m) :=
  ∑ i, (S i).val.map (fun v => toLex (v, i))

private theorem wmiPack_card {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) :
    (wmiPack k S).card = ∑ i, k i := by
  unfold wmiPack
  rw [Multiset.card_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Multiset.card_map, (S i).2]

private theorem wmi_filter_finset_sum {ι α : Type*} (p : α → Prop)
    [DecidablePred p] (s : Finset ι) (f : ι → Multiset α) :
    (∑ i ∈ s, f i).filter p = ∑ i ∈ s, (f i).filter p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Multiset.filter_add, ih, Finset.sum_insert ha]

private theorem wmiPack_filter {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) (i : Fin m) :
    (wmiPack k S).filter (fun q => (ofLex q).2 = i) =
      (S i).val.map (fun v => toLex (v, i)) := by
  classical
  unfold wmiPack
  rw [wmi_filter_finset_sum]
  simp only [Multiset.filter_map]
  rw [Finset.sum_eq_single i]
  · congr 1
    apply Multiset.filter_eq_self.mpr
    intro a _
    rfl
  · intro b _ hbi
    simp [hbi]
  · simp

private def wmiPackSym {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) :
    wmiPairSymData m (∑ i, k i) x k :=
  ⟨⟨wmiPack k S, wmiPack_card k S⟩, fun i => by
    change ((wmiPack k S).filter (fun q => (ofLex q).2 = i)).card = k i
    rw [wmiPack_filter, Multiset.card_map, (S i).2]⟩

private def wmiUnpack {m x : ℕ} (k : Fin m → ℕ)
    (M : wmiPairSymData m (∑ i, k i) x k) :
    ∀ i, Sym (Fin x) (k i) :=
  fun i =>
    ⟨M.1.val.filter (fun q => (ofLex q).2 = i) |>.map
        (fun q => (ofLex q).1),
      by rw [Multiset.card_map, M.2 i]⟩

private theorem wmiUnpack_pack {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) :
    wmiUnpack k (wmiPackSym k S) = S := by
  funext i
  apply Sym.ext
  change ((wmiPack k S).filter (fun q => (ofLex q).2 = i)).map
    (fun q => (ofLex q).1) = (S i).val
  rw [wmiPack_filter, Multiset.map_map]
  simp [Function.comp_def]

private theorem wmiPack_unpack_piece {m x : ℕ} (k : Fin m → ℕ)
    (M : wmiPairSymData m (∑ i, k i) x k) (i : Fin m) :
    ((wmiUnpack k M i).val.map (fun v => toLex (v, i))) =
      M.1.val.filter (fun q => (ofLex q).2 = i) := by
  change ((M.1.val.filter (fun q => (ofLex q).2 = i)).map
    (fun q => (ofLex q).1)).map (fun v => toLex (v, i)) = _
  rw [Multiset.map_map]
  calc
    _ = (M.1.val.filter (fun q => (ofLex q).2 = i)).map id := by
      apply Multiset.map_congr rfl
      intro q hq
      have hi : (ofLex q).2 = i := (Multiset.mem_filter.mp hq).2
      change toLex ((ofLex q).1, i) = q
      have hp : ((ofLex q).1, i) = ofLex q := Prod.ext rfl hi.symm
      rw [hp]
      exact toLex.apply_symm_apply q
    _ = _ := Multiset.map_id _

private theorem wmiPack_unpack {m x : ℕ} (k : Fin m → ℕ)
    (M : wmiPairSymData m (∑ i, k i) x k) :
    wmiPackSym k (wmiUnpack k M) = M := by
  apply Subtype.ext
  apply Sym.ext
  change wmiPack k (wmiUnpack k M) = M.1.val
  unfold wmiPack
  calc
    (∑ i, (wmiUnpack k M i).val.map (fun v => toLex (v, i))) =
        ∑ i, M.1.val.filter (fun q => (ofLex q).2 = i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact wmiPack_unpack_piece k M i
    _ = M.1.val := wmi_sum_filter_fibers M.1.val (fun q => (ofLex q).2)

private def wmiTuplePairSymEquiv (m x : ℕ) (k : Fin m → ℕ) :
    (∀ i, Sym (Fin x) (k i)) ≃
      wmiPairSymData m (∑ i, k i) x k where
  toFun := wmiPackSym k
  invFun := wmiUnpack k
  left_inv := wmiUnpack_pack k
  right_inv := wmiPack_unpack k

private def wmiTupleWordEquiv (m x : ℕ) (k : Fin m → ℕ) :
    (∀ i, Sym (Fin x) (k i)) ≃
      wmiWordData m (∑ i, k i) x k :=
  (wmiTuplePairSymEquiv m x k).trans
    ((wmiPairSymEquiv m (∑ i, k i) x k).symm.trans
      (wmiWordPairEquiv m (∑ i, k i) x k).symm)

private theorem wmi_lhs_eq_word_sum (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
    Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
      ∑ w : { w : Fin (∑ i, k i) → Fin m //
          ∀ i, Fintype.card { j : Fin (∑ i, k i) // w j = i } = k i },
        Nat.choose
          (x + (∑ i, k i) -
            ((Finset.univ.filter (fun j : Fin (∑ i, k i) =>
              ∃ h : j.val + 1 < ∑ i, k i,
                w.1 j > w.1 ⟨j.val + 1, h⟩)).card + 1)) (∑ i, k i) := by
  rw [worpitzky_lhs_card]
  rw [Fintype.card_congr (wmiTupleWordEquiv m x k)]
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro w _
  exact wmi_card_isMono w.1

private theorem wmi_descent_succ_le_max {m K : ℕ} (w : Fin K → Fin m) :
    (Finset.univ.filter (fun j : Fin K =>
      ∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩)).card + 1 ≤ max 1 K := by
  rw [← wmi_desPrefix_eq_card]
  by_cases hK : K = 0
  · subst K
    simp [desPrefix_zero]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    rw [desPrefix_last w hKpos]
    have hle := desPrefix_le_self w (K - 1)
    omega

private abbrev wmiWords (m : ℕ) (k : Fin m → ℕ) :=
  { w : Fin (∑ i, k i) → Fin m //
    ∀ i, Fintype.card { j : Fin (∑ i, k i) // w j = i } = k i }

private def wmiDesClass {m K : ℕ} (w : Fin K → Fin m) : ℕ :=
  (Finset.univ.filter (fun j : Fin K =>
    ∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩)).card + 1

private theorem wmiDesClass_le_max {m K : ℕ} (w : Fin K → Fin m) :
    wmiDesClass w ≤ max 1 K :=
  wmi_descent_succ_le_max w

private theorem wmi_regroup (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
    (∑ w : wmiWords m k,
      Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i)) =
      ∑ p ∈ Finset.Icc 1 (max 1 (∑ i, k i)),
        Nat.choose (x + (∑ i, k i) - p) (∑ i, k i) *
          Fintype.card { w : wmiWords m k // wmiDesClass w.1 = p } := by
  classical
  have hmap : ∀ w ∈ (Finset.univ : Finset (wmiWords m k)),
      wmiDesClass w.1 ∈ Finset.Icc 1 (max 1 (∑ i, k i)) := by
    intro w _
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by
      unfold wmiDesClass
      omega), wmiDesClass_le_max w.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun w => Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.card_subtype]
  calc
    (∑ w ∈ (Finset.univ.filter (fun w : wmiWords m k => wmiDesClass w.1 = p)),
        Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i)) =
        ∑ _w ∈ (Finset.univ.filter
          (fun w : wmiWords m k => wmiDesClass w.1 = p)),
          Nat.choose (x + (∑ i, k i) - p) (∑ i, k i) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    _ = _ := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

private def wmiWordFiberEquiv (m : ℕ) (k : Fin m → ℕ) (p : ℕ) :
    { w : wmiWords m k // wmiDesClass w.1 = p } ≃
      { w : Fin (∑ i, k i) → Fin m //
        (∀ i, Fintype.card { j : Fin (∑ i, k i) // w j = i } = k i) ∧
        (Finset.univ.filter (fun j : Fin (∑ i, k i) =>
          ∃ h : j.val + 1 < ∑ i, k i,
            w j > w ⟨j.val + 1, h⟩)).card + 1 = p } where
  toFun w := ⟨w.1.1, w.1.2, by simpa [wmiDesClass] using w.2⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, by simpa [wmiDesClass] using w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem wmi_word_fiber_card (m : ℕ) (k : Fin m → ℕ) (p : ℕ) :
    Fintype.card { w : wmiWords m k // wmiDesClass w.1 = p } =
      Nat.card { w : Fin (∑ i, k i) → Fin m //
        (∀ i, Fintype.card { j : Fin (∑ i, k i) // w j = i } = k i) ∧
        (Finset.univ.filter (fun j : Fin (∑ i, k i) =>
          ∃ h : j.val + 1 < ∑ i, k i,
            w j > w ⟨j.val + 1, h⟩)).card + 1 = p } := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (wmiWordFiberEquiv m k p)

/-- **Worpitzky identity for multiset permutations.** Let $m$ and $x$ be natural numbers, let
$k_1, \dots, k_m$ be natural numbers with sum $K = k_1 + \dots + k_m$, and for $p \ge 1$ let
$a_p$ be the number of words $w_1 w_2 \cdots w_K$ over the alphabet $\{1, \dots, m\}$ in which
each letter $i$ occurs exactly $k_i$ times and which have exactly $p - 1$ descents, that is,
indices $j$ with $1 \le j < K$ and $w_j > w_{j+1}$. Then

$$\prod_{i=1}^{m} \binom{x + k_i - 1}{k_i} = \sum_{p=1}^{\max(1, K)} \binom{x + K - p}{K} a_p.$$

Here subtraction of natural numbers is truncated at $0$.

Source: A. Dzhumadil'daev and D. Yeliussizov, *Power Sums of Binomial
Coefficients*, Journal of Integer Sequences 16 (2013), Article 13.1.4, Theorem
Worpitzky, lines 212-217,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>, quoting
A. S. Dzhumadil'daev, *Worpitzky identity for multipermutations*, Mat. Zametki
90 (2011), 464-466.

Proves `Wanted` entry `worpitzky_identity_multiset`.
-/
theorem worpitzky_identity_multiset (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
    Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
      Finset.sum (Finset.Icc 1 (max 1 (Finset.sum Finset.univ (fun a => k a)))) (fun p =>
        Nat.choose (x + Finset.sum Finset.univ (fun a => k a) - p)
            (Finset.sum Finset.univ (fun a => k a)) *
          Nat.card { w : Fin (Finset.sum Finset.univ (fun a => k a)) → Fin m //
            (∀ i,
              Fintype.card
                  { j : Fin (Finset.sum Finset.univ (fun a => k a)) // w j = i } = k i) ∧
            (Finset.univ.filter
                (fun j : Fin (Finset.sum Finset.univ (fun a => k a)) =>
                  ∃ h : j.val + 1 < Finset.sum Finset.univ (fun a => k a),
                    w j > w ⟨j.val + 1, h⟩)).card + 1 = p }) := by
  rw [wmi_lhs_eq_word_sum]
  change (∑ w : wmiWords m k,
    Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i)) = _
  rw [wmi_regroup]
  apply Finset.sum_congr rfl
  intro p _
  rw [wmi_word_fiber_card]

end MetaMathlibExt
end
