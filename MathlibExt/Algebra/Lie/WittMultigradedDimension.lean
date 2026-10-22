/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import MathlibExt.Algebra.Lie.FreeLieMultihomogeneousComponent
public import MathlibExt.Algebra.Lie.WittMultigradedValue

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import MathlibExt.Combinatorics.Words.LyndonWord
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

private theorem wittAppend_left_lt_iff {α : Type*} [LinearOrder α]
    (s a b : List α) : s ++ a < s ++ b ↔ a < b := by
  induction s with
  | nil => simp
  | cons x s ih =>
      change List.Lex (· < ·) (x :: (s ++ a)) (x :: (s ++ b)) ↔ a < b
      rw [List.lex_cons_iff]
      exact ih

private theorem wittAppend_right_lt_of_length_eq {α : Type*} [LinearOrder α]
    {a b : List α} (h : a < b) (hlen : a.length = b.length) (c : List α) :
    a ++ c < b ++ c := by
  change List.Lex (· < ·) a b at h
  change List.Lex (· < ·) (a ++ c) (b ++ c)
  induction h with
  | nil => simp at hlen
  | rel hab => exact .rel hab
  | cons h ih => exact .cons (ih (Nat.succ.inj hlen))

private theorem wittAppend_lt_of_lt_of_not_prefix {α : Type*} [LinearOrder α]
    {a b : List α} (h : a < b) (hp : ¬a <+: b) (c : List α) : a ++ c < b := by
  change List.Lex (· < ·) a b at h
  change List.Lex (· < ·) (a ++ c) b
  induction h with
  | @nil x l => exact (hp ⟨x :: l, rfl⟩).elim
  | rel hab => exact .rel hab
  | @cons x l₁ l₂ h ih =>
      apply List.Lex.cons
      apply ih
      intro hpre
      obtain ⟨t, ht⟩ := hpre
      exact hp ⟨t, by simp [ht]⟩

private theorem wittLe_append_self {α : Type*} [LinearOrder α] (a c : List α) :
    a ≤ a ++ c := by
  cases c with
  | nil => simp
  | cons x c =>
      apply le_of_lt
      change List.Lex (· < ·) a (a ++ x :: c)
      induction a with
      | nil => exact .nil
      | cons y a ih => exact .cons ih

private theorem wittAppend_lt_right_imp_left_lt {α : Type*} [LinearOrder α]
    {a b : List α} (h : a ++ b < b) : a < b := by
  by_contra hab
  have hba : b ≤ a := le_of_not_gt hab
  rcases hba.eq_or_lt with hba | hba
  · subst b
    exact (not_lt_of_ge (wittLe_append_self a a)) h
  · by_cases hp : b <+: a
    · obtain ⟨t, ht⟩ := hp
      have hbpre : b <+: a ++ b := by
        exact ⟨t ++ b, by simpa [List.append_assoc] using congr_arg (fun z => z ++ b) ht⟩
      obtain ⟨z, hz⟩ := hbpre
      have hble : b ≤ a ++ b := by rw [← hz]; exact wittLe_append_self b z
      exact (not_lt_of_ge hble) h
    · have hlt : b ++ b < a := wittAppend_lt_of_lt_of_not_prefix hba hp b
      have hcycle : b ++ b < b :=
        (hlt.trans_le (wittLe_append_self a b)).trans h
      exact (not_lt_of_ge (wittLe_append_self b b)) hcycle

private def WittSuffixLyndon {α : Type*} [LinearOrder α] (w : List α) : Prop :=
  w ≠ [] ∧ ∀ u v, u ≠ [] → v ≠ [] → w = u ++ v → w < v

private theorem wittLyndon_iff_suffix {α : Type*} [LinearOrder α] (w : List α) :
    IsLyndonWord w ↔ WittSuffixLyndon w := by
  constructor
  · rintro ⟨hwne, hrot⟩
    refine ⟨hwne, ?_⟩
    intro u v hune hvne hw
    subst w
    have hu0 : 0 < u.length := List.length_pos_of_ne_nil hune
    have hv0 : 0 < v.length := List.length_pos_of_ne_nil hvne
    have hlen : u.length < (u ++ v).length := by
      rw [List.length_append]
      exact Nat.lt_add_of_pos_right hv0
    have h₁ := hrot u.length hu0 hlen
    rw [List.rotate_append_length_eq] at h₁
    by_contra huv
    have hvw : v < u ++ v := lt_of_le_of_ne (le_of_not_gt huv) (by
      intro h
      have := congr_arg List.length h
      simp only [List.length_append] at this
      omega)
    by_cases hp : v <+: u ++ v
    · obtain ⟨t, ht⟩ := hp
      have htlen : t.length = u.length := by
        have := congr_arg List.length ht
        simp at this ⊢
        omega
      have htu : t < u := by
        rw [← ht, wittAppend_left_lt_iff] at h₁
        exact h₁
      have htuv : t ++ v < u ++ v := wittAppend_right_lt_of_length_eq htu htlen v
      have h₂ := hrot v.length hv0 (by simp; omega)
      rw [← ht, List.rotate_append_length_eq] at h₂
      rw [← ht] at htuv
      exact lt_asymm h₂ htuv
    · have hvrot : v ++ u < u ++ v := wittAppend_lt_of_lt_of_not_prefix hvw hp u
      exact lt_asymm h₁ hvrot
  · rintro ⟨hwne, hsuffix⟩
    refine ⟨hwne, ?_⟩
    intro k hk0 hk
    let u := w.take k
    let v := w.drop k
    have hune : u ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp [u]
      omega
    have hvne : v ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp [v]
      omega
    have hw : w = u ++ v := (List.take_append_drop k w).symm
    have hwv : w < v := hsuffix u v hune hvne hw
    rw [List.rotate_eq_drop_append_take hk.le]
    change w < v ++ u
    change List.Lex (· < ·) w (v ++ u)
    exact List.Lex.append_right (· < ·) u hwv

private theorem wittSuffixLyndon_singleton {α : Type*} [LinearOrder α] (a : α) :
    WittSuffixLyndon [a] := by
  refine ⟨by simp, ?_⟩
  intro u v hu hv h
  have hu0 := List.length_pos_of_ne_nil hu
  have hv0 := List.length_pos_of_ne_nil hv
  have := congr_arg List.length h
  simp only [List.length_cons, List.length_nil, List.length_append] at this
  omega

private theorem wittAppend_lt_right_of_lyndon_lt {α : Type*} [LinearOrder α]
    {u v : List α} (hu : u ≠ []) (hv : WittSuffixLyndon v) (huv : u < v) :
    u ++ v < v := by
  by_cases hp : u <+: v
  · obtain ⟨t, ht⟩ := hp
    have htne : t ≠ [] := by
      intro ht0
      subst t
      simp only [List.append_nil] at ht
      subst v
      exact lt_irrefl u huv
    have hvt : v < t := hv.2 u t hu htne ht.symm
    rw [← ht, wittAppend_left_lt_iff]
    rw [← ht] at hvt
    exact hvt
  · exact wittAppend_lt_of_lt_of_not_prefix huv hp v

private theorem wittSuffixLyndon_append {α : Type*} [LinearOrder α]
    {u v : List α} (hu : WittSuffixLyndon u) (hv : WittSuffixLyndon v) (huv : u < v) :
    WittSuffixLyndon (u ++ v) := by
  have huv_v : u ++ v < v := wittAppend_lt_right_of_lyndon_lt hu.1 hv huv
  refine ⟨by simp [hu.1], ?_⟩
  intro a s hane hsne heq
  rcases List.append_eq_append_iff.mp heq with h | h
  · obtain ⟨x, ha, hvx⟩ := h
    by_cases hx : x = []
    · subst x
      simp only [List.nil_append] at hvx
      subst s
      exact huv_v
    · exact huv_v.trans (hv.2 x s hx hsne hvx)
  · obtain ⟨x, hua, hsx⟩ := h
    by_cases hx : x = []
    · subst x
      simp only [List.nil_append] at hsx
      subst s
      exact huv_v
    · have hux : u < x := hu.2 a x hane hx hua
      have hnpre : ¬u <+: x := by
        intro hp
        obtain ⟨z, hz⟩ := hp
        have hlen₁ := congr_arg List.length hua
        have hlen₂ := congr_arg List.length hz
        simp only [List.length_append] at hlen₁ hlen₂
        have ha0 := List.length_pos_of_ne_nil hane
        omega
      have hlt : u ++ v < x := wittAppend_lt_of_lt_of_not_prefix hux hnpre v
      have hlt' : u ++ v < x ++ v := by
        change List.Lex (· < ·) (u ++ v) (x ++ v)
        exact List.Lex.append_right (· < ·) v hlt
      simpa [hsx] using hlt'

private theorem wittExists_lyndonSuffixIndex {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    ∃ k, 0 < k ∧ k < w.length ∧ WittSuffixLyndon (w.drop k) := by
  let k := w.length - 1
  have hk0 : 0 < k := by dsimp [k]; omega
  have hkw : k < w.length := by dsimp [k]; omega
  have hlen : (w.drop k).length = 1 := by simp [k]; omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨k, hk0, hkw, ha ▸ wittSuffixLyndon_singleton a⟩

private noncomputable def wittLongestLyndonSuffixIndex {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) : ℕ := by
  classical
  exact Nat.find (wittExists_lyndonSuffixIndex w hw)

private theorem wittLongestLyndonSuffixIndex_spec {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    0 < wittLongestLyndonSuffixIndex w hw ∧
      wittLongestLyndonSuffixIndex w hw < w.length ∧
      WittSuffixLyndon (w.drop (wittLongestLyndonSuffixIndex w hw)) := by
  classical
  exact Nat.find_spec (wittExists_lyndonSuffixIndex w hw)

private theorem wittLongestLyndonSuffixIndex_min {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) {j : ℕ}
    (hj0 : 0 < j) (hjw : j < w.length) (hj : WittSuffixLyndon (w.drop j)) :
    wittLongestLyndonSuffixIndex w hw ≤ j := by
  classical
  exact Nat.find_min' (wittExists_lyndonSuffixIndex w hw) ⟨hj0, hjw, hj⟩

private noncomputable def wittLongestLyndonPrefix {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) : List α :=
  w.take (wittLongestLyndonSuffixIndex w hw)

private noncomputable def wittLongestLyndonSuffix {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) : List α :=
  w.drop (wittLongestLyndonSuffixIndex w hw)

private theorem wittLongestLyndon_append {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    w = wittLongestLyndonPrefix w hw ++ wittLongestLyndonSuffix w hw := by
  exact (List.take_append_drop (wittLongestLyndonSuffixIndex w hw) w).symm

private theorem wittLongestLyndonPrefix_ne_nil {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) : wittLongestLyndonPrefix w hw ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [wittLongestLyndonPrefix, List.length_take,
    min_eq_left (wittLongestLyndonSuffixIndex_spec w hw).2.1.le]
  exact (wittLongestLyndonSuffixIndex_spec w hw).1

private theorem wittLongestLyndonSuffix_ne_nil {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) : wittLongestLyndonSuffix w hw ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [wittLongestLyndonSuffix, List.length_drop]
  have hk := (wittLongestLyndonSuffixIndex_spec w hw).2.1
  omega

private theorem wittLongestLyndonSuffix_isLyndon {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    WittSuffixLyndon (wittLongestLyndonSuffix w hw) :=
  (wittLongestLyndonSuffixIndex_spec w hw).2.2

private theorem length_wittLongestLyndonPrefix {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    (wittLongestLyndonPrefix w hw).length = wittLongestLyndonSuffixIndex w hw := by
  rw [wittLongestLyndonPrefix, List.length_take,
    min_eq_left (wittLongestLyndonSuffixIndex_spec w hw).2.1.le]

private theorem wittLongestLyndonPrefix_isLyndon_of_lt {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length)
    (hlt : w < wittLongestLyndonSuffix w hw) :
    WittSuffixLyndon (wittLongestLyndonPrefix w hw) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      let u := wittLongestLyndonPrefix w hw
      let v := wittLongestLyndonSuffix w hw
      have huv : w = u ++ v := wittLongestLyndon_append w hw
      have hu_ne : u ≠ [] := wittLongestLyndonPrefix_ne_nil w hw
      have hv_ne : v ≠ [] := wittLongestLyndonSuffix_ne_nil w hw
      have hvL : WittSuffixLyndon v := wittLongestLyndonSuffix_isLyndon w hw
      have huv_lt : u ++ v < v := huv ▸ hlt
      have hu_lt_v : u < v := wittAppend_lt_right_imp_left_lt huv_lt
      change WittSuffixLyndon u
      by_cases hu1 : u.length = 1
      · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hu1
        exact ha ▸ wittSuffixLyndon_singleton a
      · have hu2 : 2 ≤ u.length := by
          have hu0 := List.length_pos_of_ne_nil hu_ne
          omega
        let x := wittLongestLyndonPrefix u hu2
        let z := wittLongestLyndonSuffix u hu2
        have huxz : u = x ++ z := wittLongestLyndon_append u hu2
        have hx_ne : x ≠ [] := wittLongestLyndonPrefix_ne_nil u hu2
        have hz_ne : z ≠ [] := wittLongestLyndonSuffix_ne_nil u hu2
        have hzL : WittSuffixLyndon z := wittLongestLyndonSuffix_isLyndon u hu2
        have hvz : v ≤ z := by
          apply le_of_not_gt
          intro hzv
          have hzvL : WittSuffixLyndon (z ++ v) := wittSuffixLyndon_append hzL hvL hzv
          have hdrop : w.drop x.length = z ++ v := by
            rw [huv, huxz]
            simp [List.append_assoc]
          have hx0 : 0 < x.length := List.length_pos_of_ne_nil hx_ne
          have hxw : x.length < w.length := by
            have hz0 := List.length_pos_of_ne_nil hz_ne
            have hv0 := List.length_pos_of_ne_nil hv_ne
            simp only [huv, huxz, List.length_append]
            omega
          have hmin := wittLongestLyndonSuffixIndex_min w hw hx0 hxw (hdrop ▸ hzvL)
          have hku : wittLongestLyndonSuffixIndex w hw = u.length := by
            rw [← length_wittLongestLyndonPrefix w hw]
          have hxu : x.length < u.length := by
            have hz0 := List.length_pos_of_ne_nil hz_ne
            rw [huxz, List.length_append]
            omega
          omega
        have hu_lt_z : u < z := hu_lt_v.trans_le hvz
        have hxu : x < z := by
          have hxz_lt : x ++ z < z := huxz ▸ hu_lt_z
          exact wittAppend_lt_right_imp_left_lt hxz_lt
        have hxL : WittSuffixLyndon x := by
          apply ih u.length
          · calc
              u.length < (u ++ v).length := by
                rw [List.length_append]
                exact Nat.lt_add_of_pos_right (List.length_pos_of_ne_nil hv_ne)
              _ = w.length := congr_arg List.length huv.symm
              _ = n := hn
          · exact hu_lt_z
          · rfl
        have huL : WittSuffixLyndon (x ++ z) := wittSuffixLyndon_append hxL hzL hxu
        exact huxz ▸ huL

private theorem wittStandardFactorization {α : Type*} [LinearOrder α]
    {w : List α} (hw : IsLyndonWord w) (hw2 : 2 ≤ w.length) :
    IsLyndonWord (wittLongestLyndonPrefix w hw2) ∧
      IsLyndonWord (wittLongestLyndonSuffix w hw2) ∧
      wittLongestLyndonPrefix w hw2 < wittLongestLyndonSuffix w hw2 := by
  have hwS := (wittLyndon_iff_suffix w).mp hw
  have hlt : w < wittLongestLyndonSuffix w hw2 :=
    hwS.2 _ _ (wittLongestLyndonPrefix_ne_nil w hw2)
      (wittLongestLyndonSuffix_ne_nil w hw2) (wittLongestLyndon_append w hw2)
  have hpS := wittLongestLyndonPrefix_isLyndon_of_lt w hw2 hlt
  have hsS := wittLongestLyndonSuffix_isLyndon w hw2
  refine ⟨(wittLyndon_iff_suffix _).mpr hpS, (wittLyndon_iff_suffix _).mpr hsS, ?_⟩
  have happ_lt : wittLongestLyndonPrefix w hw2 ++ wittLongestLyndonSuffix w hw2 <
      wittLongestLyndonSuffix w hw2 := (wittLongestLyndon_append w hw2) ▸ hlt
  exact wittAppend_lt_right_imp_left_lt happ_lt

private noncomputable def wittLyndonBracket (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) (hw : IsLyndonWord w) : FreeLieAlgebra K (Fin r) :=
  if hlen : w.length = 1 then
    FreeLieAlgebra.of K (w.head hw.1)
  else
    let hw2 : 2 ≤ w.length := by
      have hw0 := List.length_pos_of_ne_nil hw.1
      omega
    let hfac := wittStandardFactorization hw hw2
    ⁅wittLyndonBracket K (wittLongestLyndonPrefix w hw2) hfac.1,
      wittLyndonBracket K (wittLongestLyndonSuffix w hw2) hfac.2.1⁆
termination_by w.length
decreasing_by
  · rw [length_wittLongestLyndonPrefix]
    exact (wittLongestLyndonSuffixIndex_spec w hw2).2.1
  · rw [wittLongestLyndonSuffix, List.length_drop]
    have hk := (wittLongestLyndonSuffixIndex_spec w hw2).1
    omega

private theorem wittLyndonBracket_isMonomial (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) (hw : IsLyndonWord w) :
    IsFreeLieMonomial K (wittWordContent w) (wittLyndonBracket K w hw) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      rw [wittLyndonBracket]
      split_ifs with hlen
      · obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hlen
        convert IsFreeLieMonomial.gen (K := K) i using 1
        · ext j
          by_cases hji : j = i
          · subst j
            simp [wittWordContent]
          · simp [wittWordContent, hji, Ne.symm hji]
        · simp
      · have hw2 : 2 ≤ w.length := by
          have hw0 := List.length_pos_of_ne_nil hw.1
          omega
        let u := wittLongestLyndonPrefix w hw2
        let v := wittLongestLyndonSuffix w hw2
        have hfac := wittStandardFactorization hw hw2
        have hu_len : u.length < n := by
          rw [← hn, length_wittLongestLyndonPrefix]
          exact (wittLongestLyndonSuffixIndex_spec w hw2).2.1
        have hv_len : v.length < n := by
          change (wittLongestLyndonSuffix w hw2).length < n
          rw [← hn, wittLongestLyndonSuffix, List.length_drop]
          have hk := (wittLongestLyndonSuffixIndex_spec w hw2).1
          omega
        have hu := ih u.length hu_len u hfac.1 rfl
        have hv := ih v.length hv_len v hfac.2.1 rfl
        have huv : wittWordContent w = fun i => wittWordContent u i + wittWordContent v i := by
          rw [wittLongestLyndon_append w hw2, wittWordContent_append]
        rw [huv]
        exact IsFreeLieMonomial.bracket hu hv

private noncomputable def wittAssocWord (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : FreeAlgebra K (Fin r) :=
  FreeAlgebra.basisFreeMonoid K (Fin r) (FreeMonoid.ofList w)

private theorem wittAssocWord_mul (K : Type) [Field K] {r : ℕ}
    (u v : List (Fin r)) :
    wittAssocWord K u * wittAssocWord K v = wittAssocWord K (u ++ v) := by
  rw [show wittAssocWord K u =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid).symm
        (MonoidAlgebra.single (FreeMonoid.ofList u) 1) by rfl]
  rw [show wittAssocWord K v =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid).symm
        (MonoidAlgebra.single (FreeMonoid.ofList v) 1) by rfl]
  rw [← map_mul, MonoidAlgebra.single_mul_single, one_mul]
  rfl

private theorem wittAssocWord_singleton (K : Type) [Field K] {r : ℕ} (i : Fin r) :
    wittAssocWord K [i] = FreeAlgebra.ι K i := by
  rw [wittAssocWord, FreeMonoid.ofList_singleton]
  apply (FreeAlgebra.basisFreeMonoid K (Fin r)).repr.injective
  rw [Module.Basis.repr_self]
  ext w
  simp [FreeAlgebra.basisFreeMonoid, FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private def WittWordsGE {r : ℕ} (w : List (Fin r)) : Set (List (Fin r)) :=
  {z | wittWordContent z = wittWordContent w ∧ w ≤ z}

private def WittWordsGT {r : ℕ} (w : List (Fin r)) : Set (List (Fin r)) :=
  {z | wittWordContent z = wittWordContent w ∧ w < z}

private noncomputable def wittWordSpanGE (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : Submodule K (FreeAlgebra K (Fin r)) :=
  Submodule.span K (wittAssocWord K '' WittWordsGE w)

private noncomputable def wittWordSpanGT (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : Submodule K (FreeAlgebra K (Fin r)) :=
  Submodule.span K (wittAssocWord K '' WittWordsGT w)

private theorem wittWordContent_eq_length_eq {r : ℕ} {u v : List (Fin r)}
    (h : wittWordContent u = wittWordContent v) : u.length = v.length := by
  rw [← sum_wittWordContent u, ← sum_wittWordContent v, h]

private theorem wittAssocWord_mem_spanGE (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : wittAssocWord K w ∈ wittWordSpanGE K w := by
  apply Submodule.subset_span
  exact ⟨w, ⟨rfl, le_rfl⟩, rfl⟩

private theorem wittWordSpanGT_le_spanGE (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : wittWordSpanGT K w ≤ wittWordSpanGE K w := by
  apply Submodule.span_mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1, hz.2.le⟩, rfl⟩

private theorem witt_mul_mem_wordSpan (K : Type) [Field K] {r : ℕ}
    {S T U : Set (List (Fin r))}
    (hmul : ∀ u ∈ S, ∀ v ∈ T, u ++ v ∈ U)
    {x y : FreeAlgebra K (Fin r)}
    (hx : x ∈ Submodule.span K (wittAssocWord K '' S))
    (hy : y ∈ Submodule.span K (wittAssocWord K '' T)) :
    x * y ∈ Submodule.span K (wittAssocWord K '' U) := by
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (Submodule.span K (wittAssocWord K '' U))
      (wittAssocWord K '' S) (wittAssocWord K '' T) (LinearMap.mul K _)
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    change wittAssocWord K u * wittAssocWord K v ∈ _
    rw [wittAssocWord_mul]
    exact Submodule.subset_span ⟨u ++ v, hmul u hu v hv, rfl⟩
  · exact hx
  · exact hy

private theorem wittAppend_le_append_of_le_of_le {α : Type*} [LinearOrder α]
    {u u' v v' : List α} (hu : u ≤ u') (hlen : u.length = u'.length)
    (hv : v ≤ v') : u ++ v ≤ u' ++ v' := by
  rcases hu.eq_or_lt with rfl | hu
  · rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact ((wittAppend_left_lt_iff u v v').mpr hv).le
  · apply (wittAppend_right_lt_of_length_eq hu hlen v).le.trans
    rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact ((wittAppend_left_lt_iff u' v v').mpr hv).le

private theorem wittAppend_lt_append_of_lt_of_le {α : Type*} [LinearOrder α]
    {u u' v v' : List α} (hu : u < u') (hlen : u.length = u'.length)
    (hv : v ≤ v') : u ++ v < u' ++ v' :=
  (wittAppend_right_lt_of_length_eq hu hlen v).trans_le (by
    rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact ((wittAppend_left_lt_iff u' v v').mpr hv).le)

private theorem wittAppend_lt_append_of_le_of_lt {α : Type*} [LinearOrder α]
    {u u' v v' : List α} (hu : u ≤ u') (hlen : u.length = u'.length)
    (hv : v < v') : u ++ v < u' ++ v' := by
  rcases hu.eq_or_lt with rfl | hu
  · exact (wittAppend_left_lt_iff u v v').mpr hv
  · exact (wittAppend_right_lt_of_length_eq hu hlen v).trans
      ((wittAppend_left_lt_iff u' v v').mpr hv)

private theorem wittWordSpanGE_mul_spanGE (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : x ∈ wittWordSpanGE K u) (hy : y ∈ wittWordSpanGE K v) :
    x * y ∈ wittWordSpanGE K (u ++ v) := by
  apply witt_mul_mem_wordSpan K (S := WittWordsGE u) (T := WittWordsGE v)
  · intro u' hu' v' hv'
    refine ⟨?_, ?_⟩
    · rw [wittWordContent_append, wittWordContent_append, hu'.1, hv'.1]
    · exact wittAppend_le_append_of_le_of_le hu'.2
        (wittWordContent_eq_length_eq hu'.1.symm) hv'.2
  · exact hx
  · exact hy

private theorem wittWordSpanGT_mul_spanGE (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : x ∈ wittWordSpanGT K u) (hy : y ∈ wittWordSpanGE K v) :
    x * y ∈ wittWordSpanGT K (u ++ v) := by
  apply witt_mul_mem_wordSpan K (S := WittWordsGT u) (T := WittWordsGE v)
  · intro u' hu' v' hv'
    refine ⟨?_, ?_⟩
    · rw [wittWordContent_append, wittWordContent_append, hu'.1, hv'.1]
    · exact wittAppend_lt_append_of_lt_of_le hu'.2
        (wittWordContent_eq_length_eq hu'.1.symm) hv'.2
  · exact hx
  · exact hy

private theorem wittWordSpanGE_mul_spanGT (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : x ∈ wittWordSpanGE K u) (hy : y ∈ wittWordSpanGT K v) :
    x * y ∈ wittWordSpanGT K (u ++ v) := by
  apply witt_mul_mem_wordSpan K (S := WittWordsGE u) (T := WittWordsGT v)
  · intro u' hu' v' hv'
    refine ⟨?_, ?_⟩
    · rw [wittWordContent_append, wittWordContent_append, hu'.1, hv'.1]
    · exact wittAppend_lt_append_of_le_of_lt hu'.2
        (wittWordContent_eq_length_eq hu'.1.symm) hv'.2
  · exact hx
  · exact hy

private theorem wittWordSpanGE_le_spanGT_of_lt (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} (hcontent : wittWordContent v = wittWordContent u)
    (hlt : u < v) : wittWordSpanGE K v ≤ wittWordSpanGT K u := by
  apply Submodule.span_mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1.trans hcontent, hlt.trans_le hz.2⟩, rfl⟩

private def WittTriangular (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) (x : FreeAlgebra K (Fin r)) : Prop :=
  x - wittAssocWord K w ∈ wittWordSpanGT K w

private theorem wittTriangular_mem_spanGE (K : Type) [Field K] {r : ℕ}
    {w : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hx : WittTriangular K w x) :
    x ∈ wittWordSpanGE K w := by
  rw [← sub_add_cancel x (wittAssocWord K w)]
  exact Submodule.add_mem _ (wittWordSpanGT_le_spanGE K w hx)
    (wittAssocWord_mem_spanGE K w)

private theorem wittTriangular_mul (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : WittTriangular K u x) (hy : WittTriangular K v y) :
    x * y - wittAssocWord K (u ++ v) ∈ wittWordSpanGT K (u ++ v) := by
  rw [← wittAssocWord_mul]
  have hxy : x * y - wittAssocWord K u * wittAssocWord K v =
      (x - wittAssocWord K u) * y + wittAssocWord K u * (y - wittAssocWord K v) := by
    rw [sub_mul, mul_sub]
    abel
  rw [hxy]
  apply Submodule.add_mem
  · exact wittWordSpanGT_mul_spanGE K hx (wittTriangular_mem_spanGE K hy)
  · exact wittWordSpanGE_mul_spanGT K (wittAssocWord_mem_spanGE K u) hy

private theorem wittTriangular_reverse_mul (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : WittTriangular K u x) (hy : WittTriangular K v y)
    (hlt : u ++ v < v ++ u) : y * x ∈ wittWordSpanGT K (u ++ v) := by
  have hcontent : wittWordContent (v ++ u) = wittWordContent (u ++ v) := by
    rw [wittWordContent_append, wittWordContent_append]
    funext i
    exact Nat.add_comm _ _
  exact (wittWordSpanGE_le_spanGT_of_lt K hcontent hlt)
    (wittWordSpanGE_mul_spanGE K
      (wittTriangular_mem_spanGE K hy) (wittTriangular_mem_spanGE K hx))

private theorem wittLyndon_append_lt_swap {α : Type*} [LinearOrder α]
    {u v : List α} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (huv : u < v) :
    u ++ v < v ++ u := by
  have huvL : WittSuffixLyndon (u ++ v) :=
    wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
      ((wittLyndon_iff_suffix v).mp hv) huv
  exact (huvL.2 u v hu.1 hv.1 rfl).trans_le (wittLe_append_self v u)

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def wittAssocLift (K : Type) [Field K] {r : ℕ} :
    FreeLieAlgebra K (Fin r) →ₗ⁅K⁆ FreeAlgebra K (Fin r) :=
  FreeLieAlgebra.lift K (FreeAlgebra.ι K)

private theorem wittAssocLift_lyndonBracket_triangular (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) (hw : IsLyndonWord w) :
    WittTriangular K w (wittAssocLift K (wittLyndonBracket K w hw)) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      rw [wittLyndonBracket]
      split_ifs with hlen
      · obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hlen
        unfold WittTriangular
        rw [wittAssocLift, FreeLieAlgebra.lift_of_apply]
        simp only [List.head_cons]
        rw [← wittAssocWord_singleton]
        simp
      · have hw2 : 2 ≤ w.length := by
          have hw0 := List.length_pos_of_ne_nil hw.1
          omega
        let u := wittLongestLyndonPrefix w hw2
        let v := wittLongestLyndonSuffix w hw2
        have hfac := wittStandardFactorization hw hw2
        have hu_len : u.length < n := by
          rw [← hn, length_wittLongestLyndonPrefix]
          exact (wittLongestLyndonSuffixIndex_spec w hw2).2.1
        have hv_len : v.length < n := by
          change (wittLongestLyndonSuffix w hw2).length < n
          rw [← hn, wittLongestLyndonSuffix, List.length_drop]
          have hk := (wittLongestLyndonSuffixIndex_spec w hw2).1
          omega
        have hu := ih u.length hu_len u hfac.1 rfl
        have hv := ih v.length hv_len v hfac.2.1 rfl
        have hswap : u ++ v < v ++ u :=
          wittLyndon_append_lt_swap hfac.1 hfac.2.1 hfac.2.2
        have hmul := wittTriangular_mul K hu hv
        have hrev := wittTriangular_reverse_mul K hu hv hswap
        unfold WittTriangular
        rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
        have heq :
            (wittAssocLift K (wittLyndonBracket K u hfac.1) *
                wittAssocLift K (wittLyndonBracket K v hfac.2.1) -
              wittAssocLift K (wittLyndonBracket K v hfac.2.1) *
                wittAssocLift K (wittLyndonBracket K u hfac.1)) -
                wittAssocWord K (u ++ v) =
              (wittAssocLift K (wittLyndonBracket K u hfac.1) *
                  wittAssocLift K (wittLyndonBracket K v hfac.2.1) -
                wittAssocWord K (u ++ v)) -
              wittAssocLift K (wittLyndonBracket K v hfac.2.1) *
                wittAssocLift K (wittLyndonBracket K u hfac.1) := by
          abel
        have hfinal :
            (wittAssocLift K (wittLyndonBracket K u hfac.1) *
                wittAssocLift K (wittLyndonBracket K v hfac.2.1) -
              wittAssocLift K (wittLyndonBracket K v hfac.2.1) *
                wittAssocLift K (wittLyndonBracket K u hfac.1)) -
                wittAssocWord K (u ++ v) ∈ wittWordSpanGT K (u ++ v) := by
          rw [heq]
          exact Submodule.sub_mem _ hmul hrev
        have hwuv : w = u ++ v := wittLongestLyndon_append w hw2
        rw [← hwuv] at hfinal
        exact hfinal

private theorem wittWordSpanGT_repr_eq_zero (K : Type) [Field K] {r : ℕ}
    {w q : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hq : ¬w < q)
    (hx : x ∈ wittWordSpanGT K w) :
    (FreeAlgebra.basisFreeMonoid K (Fin r)).repr x (FreeMonoid.ofList q) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨z, hz, rfl⟩
      rw [wittAssocWord, Module.Basis.repr_self]
      apply Finsupp.single_eq_of_ne
      intro heq
      have hqz : q = z := FreeMonoid.ofList.injective heq
      exact hq (hqz ▸ hz.2)
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

private theorem wittTriangular_repr_self (K : Type) [Field K] {r : ℕ}
    {w : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hx : WittTriangular K w x) :
    (FreeAlgebra.basisFreeMonoid K (Fin r)).repr x (FreeMonoid.ofList w) = 1 := by
  have hzero := wittWordSpanGT_repr_eq_zero K (w := w) (q := w) (lt_irrefl w) hx
  rw [map_sub, Finsupp.sub_apply] at hzero
  rw [wittAssocWord, Module.Basis.repr_self, Finsupp.single_eq_same] at hzero
  exact sub_eq_zero.mp hzero

private theorem wittTriangular_repr_eq_zero_of_lt (K : Type) [Field K] {r : ℕ}
    {w q : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hx : WittTriangular K w x)
    (hqw : q < w) :
    (FreeAlgebra.basisFreeMonoid K (Fin r)).repr x (FreeMonoid.ofList q) = 0 := by
  have hzero := wittWordSpanGT_repr_eq_zero K (w := w) (q := q)
    (not_lt_of_ge hqw.le) hx
  rw [map_sub, Finsupp.sub_apply] at hzero
  have hne : FreeMonoid.ofList q ≠ FreeMonoid.ofList w := by
    exact fun heq => hqw.ne (FreeMonoid.ofList.injective heq)
  rw [wittAssocWord, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne, sub_zero] at hzero
  exact hzero

private noncomputable def wittLyndonFamily (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) (w : LyndonWordsOfContent degree) :
    FreeLieAlgebra K (Fin r) :=
  wittLyndonBracket K w.1.1 w.2

private theorem wittAssocLyndonFamily_linearIndependent (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) :
    LinearIndependent K (fun w : LyndonWordsOfContent degree =>
      wittAssocLift K (wittLyndonFamily K degree w)) := by
  classical
  let _ : LinearOrder (LyndonWordsOfContent degree) :=
    LinearOrder.lift' (fun w => w.1.1) fun _ _ h => Subtype.ext (Subtype.ext h)
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  by_contra hi
  let s := Finset.univ.filter fun j => g j ≠ 0
  have hs : s.Nonempty := ⟨i, by simp [s, hi]⟩
  let m := s.min' hs
  have hmne : g m ≠ 0 := by
    have hm := Finset.min'_mem s hs
    simpa [s] using hm
  have hbefore : ∀ j, j < m → g j = 0 := by
    intro j hjm
    by_contra hj
    have hjmem : j ∈ s := by simp [s, hj]
    exact (not_le_of_gt hjm) (Finset.min'_le s j hjmem)
  let coord : FreeAlgebra K (Fin r) →ₗ[K] K :=
    (Finsupp.lapply (R := K) (FreeMonoid.ofList m.1.1)).comp
      (FreeAlgebra.basisFreeMonoid K (Fin r)).repr.toLinearMap
  have hcoord :
      (∑ j, g j * (FreeAlgebra.basisFreeMonoid K (Fin r)).repr
        (wittAssocLift K (wittLyndonFamily K degree j)) (FreeMonoid.ofList m.1.1)) = 0 := by
    have h := congrArg coord hsum
    simpa [coord] using h
  have hsum_single :
      (∑ j, g j * (FreeAlgebra.basisFreeMonoid K (Fin r)).repr
        (wittAssocLift K (wittLyndonFamily K degree j)) (FreeMonoid.ofList m.1.1)) = g m := by
    calc
      _ = g m * (FreeAlgebra.basisFreeMonoid K (Fin r)).repr
          (wittAssocLift K (wittLyndonFamily K degree m)) (FreeMonoid.ofList m.1.1) :=
        Fintype.sum_eq_single m (by
          intro j hjm
          rcases lt_or_gt_of_ne hjm with hjlt | hmlt
          · rw [hbefore j hjlt, zero_mul]
          · have hmlt' : m.1.1 < j.1.1 := hmlt
            rw [wittLyndonFamily, wittTriangular_repr_eq_zero_of_lt K
              (wittAssocLift_lyndonBracket_triangular K j.1.1 j.2) hmlt', mul_zero])
      _ = g m := by
        rw [wittLyndonFamily,
          wittTriangular_repr_self K
            (wittAssocLift_lyndonBracket_triangular K m.1.1 m.2), mul_one]
  rw [hsum_single] at hcoord
  exact hmne hcoord

private theorem wittLyndonFamily_linearIndependent (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) :
    LinearIndependent K (wittLyndonFamily K degree) := by
  apply LinearIndependent.of_comp (wittAssocLift K).toLinearMap
  exact wittAssocLyndonFamily_linearIndependent K degree

private theorem wittExists_lyndonSuffix_le {α : Type*} [LinearOrder α]
    (w : List α) (hw : w ≠ []) :
    ∃ a s, s ≠ [] ∧ IsLyndonWord s ∧ w = a ++ s ∧ s ≤ w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      by_cases hwL : IsLyndonWord w
      · exact ⟨[], w, hw, hwL, by simp, le_rfl⟩
      · have hnS : ¬WittSuffixLyndon w := by
          exact fun hS => hwL ((wittLyndon_iff_suffix w).mpr hS)
        have hnforall :
            ¬∀ a s, a ≠ [] → s ≠ [] → w = a ++ s → w < s := by
          exact fun h => hnS ⟨hw, h⟩
        push Not at hnforall
        obtain ⟨a, s, ha, hs, has, hws⟩ := hnforall
        have hslen : s.length < n := by
          have halen := List.length_pos_of_ne_nil ha
          rw [← hn, has, List.length_append]
          omega
        obtain ⟨b, t, ht, htL, hst, htle⟩ := ih s.length hslen s hs rfl
        refine ⟨a ++ b, t, ht, htL, ?_, htle.trans hws⟩
        rw [has, hst, List.append_assoc]

private theorem wittLongestLyndonSuffix_le_suffix {α : Type*} [LinearOrder α]
    {w : List α} (_hw : IsLyndonWord w) (hw2 : 2 ≤ w.length)
    {a q : List α} (ha : a ≠ []) (hq : q ≠ []) (hwq : w = a ++ q) :
    wittLongestLyndonSuffix w hw2 ≤ q := by
  obtain ⟨b, s, hs, hsL, hqbs, hsle⟩ := wittExists_lyndonSuffix_le q hq
  let j := (a ++ b).length
  have hwabs : w = (a ++ b) ++ s := by rw [hwq, hqbs, List.append_assoc]
  have hj0 : 0 < j := by
    dsimp [j]
    have ha0 := List.length_pos_of_ne_nil ha
    simp only [List.length_append]
    omega
  have hjw : j < w.length := by
    have hs0 := List.length_pos_of_ne_nil hs
    rw [hwabs, List.length_append]
    dsimp [j]
    omega
  have hdrop : w.drop j = s := by
    rw [hwabs]
    simp [j]
  have hdropL : WittSuffixLyndon (w.drop j) := by
    rw [hdrop]
    exact (wittLyndon_iff_suffix s).mp hsL
  have hmin : wittLongestLyndonSuffixIndex w hw2 ≤ j :=
    wittLongestLyndonSuffixIndex_min w hw2 hj0 hjw hdropL
  let c := (a ++ b).drop (wittLongestLyndonSuffixIndex w hw2)
  have hvcs : wittLongestLyndonSuffix w hw2 = c ++ s := by
    unfold wittLongestLyndonSuffix
    calc
      w.drop (wittLongestLyndonSuffixIndex w hw2) =
          ((a ++ b) ++ s).drop (wittLongestLyndonSuffixIndex w hw2) :=
        congr_arg (List.drop (wittLongestLyndonSuffixIndex w hw2)) hwabs
      _ = c ++ s := by rw [List.drop_append_of_le_length hmin]
  have hvle : wittLongestLyndonSuffix w hw2 ≤ s := by
    by_cases hc : c = []
    · simp [hvcs, hc]
    · exact (wittLongestLyndonSuffix_isLyndon w hw2).2 c s hc hs hvcs |>.le
  exact hvle.trans hsle

private theorem wittStandardFactorization_append {α : Type*} [LinearOrder α]
    {u v : List α} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (_huv : u < v)
    (hu2 : 2 ≤ u.length)
    (hvu : v ≤ wittLongestLyndonSuffix u hu2) :
    let hw2 : 2 ≤ (u ++ v).length := by
      simp only [List.length_append]
      omega
    wittLongestLyndonPrefix (u ++ v) hw2 = u ∧
      wittLongestLyndonSuffix (u ++ v) hw2 = v := by
  dsimp only
  have hw2 : 2 ≤ (u ++ v).length := by
    simp only [List.length_append]
    omega
  let k := wittLongestLyndonSuffixIndex (u ++ v) hw2
  have huk : k ≤ u.length := by
    apply wittLongestLyndonSuffixIndex_min (u ++ v) hw2
    · exact List.length_pos_of_ne_nil hu.1
    · simp only [List.length_append]
      exact Nat.lt_add_of_pos_right (List.length_pos_of_ne_nil hv.1)
    · have hdrop : (u ++ v).drop u.length = v := by simp
      rw [hdrop]
      exact (wittLyndon_iff_suffix v).mp hv
  have hku : k = u.length := by
    apply le_antisymm huk
    by_contra hnot
    have hku_lt : k < u.length := Nat.lt_of_not_ge hnot
    let q := u.drop k
    have hq : q ≠ [] := by
      apply List.ne_nil_of_length_pos
      change (u.drop k).length > 0
      rw [List.length_drop]
      omega
    have hk0 : 0 < k := (wittLongestLyndonSuffixIndex_spec (u ++ v) hw2).1
    have ht : u.take k ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_take, min_eq_left hku_lt.le]
      exact hk0
    have hu_decomp : u = u.take k ++ q := by
      exact (List.take_append_drop k u).symm
    have hbq : wittLongestLyndonSuffix u hu2 ≤ q :=
      wittLongestLyndonSuffix_le_suffix hu hu2 ht hq hu_decomp
    have hsuffix : wittLongestLyndonSuffix (u ++ v) hw2 = q ++ v := by
      rw [wittLongestLyndonSuffix, show wittLongestLyndonSuffixIndex (u ++ v) hw2 = k from rfl,
        List.drop_append_of_le_length huk]
    have hltv : wittLongestLyndonSuffix (u ++ v) hw2 < v :=
      (wittLongestLyndonSuffix_isLyndon (u ++ v) hw2).2 q v hq hv.1 hsuffix
    have hqv : q < v := by
      rw [hsuffix] at hltv
      exact wittAppend_lt_right_imp_left_lt hltv
    exact (not_lt_of_ge (hvu.trans hbq)) hqv
  constructor
  · unfold wittLongestLyndonPrefix
    change (u ++ v).take k = u
    rw [hku]
    simp
  · unfold wittLongestLyndonSuffix
    change (u ++ v).drop k = v
    rw [hku]
    simp

private theorem wittLyndonBracket_append (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (_huv : u < v)
    (hu2 : 2 ≤ u.length)
    (hvu : v ≤ wittLongestLyndonSuffix u hu2) :
    wittLyndonBracket K (u ++ v)
        ((wittLyndon_iff_suffix (u ++ v)).mpr
          (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
            ((wittLyndon_iff_suffix v).mp hv) _huv)) =
      ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ := by
  have hw2 : 2 ≤ (u ++ v).length := by
    simp only [List.length_append]
    omega
  have hfac := wittStandardFactorization_append hu hv _huv hu2 hvu
  rw [wittLyndonBracket]
  split_ifs with hlen
  · omega
  · simp only [hfac.1, hfac.2]

private theorem wittLyndonBracket_append_of_length_one (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (_huv : u < v)
    (hu1 : u.length = 1) :
    wittLyndonBracket K (u ++ v)
        ((wittLyndon_iff_suffix (u ++ v)).mpr
          (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
            ((wittLyndon_iff_suffix v).mp hv) _huv)) =
      ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ := by
  have hw2 : 2 ≤ (u ++ v).length := by
    have hv0 := List.length_pos_of_ne_nil hv.1
    simp only [List.length_append]
    omega
  let k := wittLongestLyndonSuffixIndex (u ++ v) hw2
  have huk : k ≤ u.length := by
    apply wittLongestLyndonSuffixIndex_min (u ++ v) hw2
    · rw [hu1]
      omega
    · simp only [List.length_append]
      exact Nat.lt_add_of_pos_right (List.length_pos_of_ne_nil hv.1)
    · simp only [hu1]
      have hdrop : (u ++ v).drop 1 = v := by
        obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hu1
        simp
      rw [hdrop]
      exact (wittLyndon_iff_suffix v).mp hv
  have hk : k = u.length := by
    have hk0 := (wittLongestLyndonSuffixIndex_spec (u ++ v) hw2).1
    omega
  have hp : wittLongestLyndonPrefix (u ++ v) hw2 = u := by
    unfold wittLongestLyndonPrefix
    change (u ++ v).take k = u
    rw [hk]
    simp
  have hs : wittLongestLyndonSuffix (u ++ v) hw2 = v := by
    unfold wittLongestLyndonSuffix
    change (u ++ v).drop k = v
    rw [hk]
    simp
  rw [wittLyndonBracket]
  split_ifs with hlen
  · omega
  · simp only [hp, hs]

private noncomputable def wittLyndonSpanFrom (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) (lower : List (Fin r)) :
    Submodule K (FreeLieAlgebra K (Fin r)) :=
  Submodule.span K {x | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
    wittWordContent w = degree ∧ lower ≤ w ∧ x = wittLyndonBracket K w hw}

private theorem wittLyndonBracket_mem_spanFrom (K : Type) [Field K] {r : ℕ}
    {degree : Fin r → ℕ} {lower w : List (Fin r)} (hw : IsLyndonWord w)
    (hdegree : wittWordContent w = degree) (hlower : lower ≤ w) :
    wittLyndonBracket K w hw ∈ wittLyndonSpanFrom K degree lower := by
  apply Submodule.subset_span
  exact ⟨w, hw, hdegree, hlower, rfl⟩

private theorem wittLyndonSpanFrom_mono (K : Type) [Field K] {r : ℕ}
    {degree : Fin r → ℕ} {u v : List (Fin r)} (huv : u ≤ v) :
    wittLyndonSpanFrom K degree v ≤ wittLyndonSpanFrom K degree u := by
  apply Submodule.span_mono
  rintro x ⟨w, hw, hdegree, hvw, rfl⟩
  exact ⟨w, hw, hdegree, huv.trans hvw, rfl⟩

private def WittLyndonPair (r n : ℕ) :=
  {p : List (Fin r) × List (Fin r) //
    IsLyndonWord p.1 ∧ IsLyndonWord p.2 ∧ p.1 < p.2 ∧ p.1.length + p.2.length = n}

private def wittLyndonPairEncode {r n : ℕ} (p : WittLyndonPair r n) :
    List.Vector (Fin r) n × Fin (n + 1) :=
  (⟨p.1.1 ++ p.1.2, by simpa using p.2.2.2.2⟩,
    ⟨p.1.1.length, by have := p.2.2.2.2; omega⟩)

private theorem wittLyndonPairEncode_injective {r n : ℕ} :
    Function.Injective (wittLyndonPairEncode : WittLyndonPair r n →
      List.Vector (Fin r) n × Fin (n + 1)) := by
  intro p q hpq
  have hconcat : p.1.1 ++ p.1.2 = q.1.1 ++ q.1.2 :=
    congr_arg (fun z : List.Vector (Fin r) n × Fin (n + 1) => z.1.1) hpq
  have hlen : p.1.1.length = q.1.1.length :=
    congr_arg (fun z : List.Vector (Fin r) n × Fin (n + 1) => z.2.1) hpq
  apply Subtype.ext
  apply Prod.ext
  · calc
      p.1.1 = (p.1.1 ++ p.1.2).take p.1.1.length := by simp
      _ = (q.1.1 ++ q.1.2).take p.1.1.length := congr_arg _ hconcat
      _ = q.1.1 := by rw [hlen]; simp
  · calc
      p.1.2 = (p.1.1 ++ p.1.2).drop p.1.1.length := by simp
      _ = (q.1.1 ++ q.1.2).drop p.1.1.length := congr_arg _ hconcat
      _ = q.1.2 := by rw [hlen]; simp

private instance {r n : ℕ} : Finite (WittLyndonPair r n) :=
  Finite.of_injective wittLyndonPairEncode wittLyndonPairEncode_injective

private def WittLyndonPairRel {r n : ℕ} (p q : WittLyndonPair r n) : Prop :=
  q.1.1 ++ q.1.2 < p.1.1 ++ p.1.2 ∨
    (q.1.1 ++ q.1.2 = p.1.1 ++ p.1.2 ∧ p.1.1.length < q.1.1.length)

private instance {r n : ℕ} : IsTrans (WittLyndonPair r n) WittLyndonPairRel where
  trans p q s hpq hqs := by
    rcases hpq with hpq | ⟨hpq, hpqlen⟩
    · rcases hqs with hqs | ⟨hqs, _⟩
      · exact Or.inl (hqs.trans hpq)
      · exact Or.inl (hqs ▸ hpq)
    · rcases hqs with hqs | ⟨hqs, hqslen⟩
      · exact Or.inl (hqs.trans_le hpq.le)
      · exact Or.inr ⟨hqs.trans hpq, hpqlen.trans hqslen⟩

private instance {r n : ℕ} : Std.Irrefl (@WittLyndonPairRel r n) where
  irrefl p hp := by
    rcases hp with hp | ⟨_, hp⟩
    · exact (lt_irrefl _) hp
    · exact (lt_irrefl _) hp

private theorem wittLyndonPairRel_wellFounded {r n : ℕ} :
    WellFounded (@WittLyndonPairRel r n) :=
  Finite.wellFounded_of_trans_of_irrefl _

private theorem wittLt_append_self_of_ne_nil {α : Type*} [LinearOrder α]
    (u : List α) {v : List α} (hv : v ≠ []) : u < u ++ v := by
  apply lt_of_le_of_ne (wittLe_append_self u v)
  intro h
  have hv0 := List.length_pos_of_ne_nil hv
  have := congr_arg List.length h
  simp only [List.length_append] at this
  omega

private theorem wittContent_append_replace {r : ℕ} {a x y : List (Fin r)}
    (h : wittWordContent x = wittWordContent y) :
    wittWordContent (a ++ x) = wittWordContent (a ++ y) := by
  rw [wittWordContent_append, wittWordContent_append, h]

private theorem wittContent_swap_append {r : ℕ} (u v : List (Fin r)) :
    wittWordContent (u ++ v) = wittWordContent (v ++ u) := by
  rw [wittWordContent_append, wittWordContent_append]
  funext i
  exact Nat.add_comm _ _

private theorem wittOrderedBracket_mem_spanFrom_aux (K : Type) [Field K] {r : ℕ}
    (n : ℕ) (u v : List (Fin r)) (hu : IsLyndonWord u) (hv : IsLyndonWord v)
    (huv : u < v) (hlen : u.length + v.length = n) :
    ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ ∈
      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v) := by
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
      let p0 : WittLyndonPair r n := ⟨(u, v), hu, hv, huv, hlen⟩
      have hall : ∀ p : WittLyndonPair r n,
          ⁅wittLyndonBracket K p.1.1 p.2.1,
              wittLyndonBracket K p.1.2 p.2.2.1⁆ ∈
            wittLyndonSpanFrom K (wittWordContent (p.1.1 ++ p.1.2))
              (p.1.1 ++ p.1.2) := by
        intro p
        induction p using wittLyndonPairRel_wellFounded.induction with
        | h p rec =>
            let u := p.1.1
            let v := p.1.2
            have hu : IsLyndonWord u := p.2.1
            have hv : IsLyndonWord v := p.2.2.1
            have huv : u < v := p.2.2.2.1
            have huvlen : u.length + v.length = n := p.2.2.2.2
            change ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ ∈
              wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v)
            by_cases hu1 : u.length = 1
            · let hw : IsLyndonWord (u ++ v) := (wittLyndon_iff_suffix (u ++ v)).mpr
                (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
                  ((wittLyndon_iff_suffix v).mp hv) huv)
              have heq := wittLyndonBracket_append_of_length_one K hu hv huv hu1
              exact heq ▸ wittLyndonBracket_mem_spanFrom K hw rfl le_rfl
            · have hu2 : 2 ≤ u.length := by
                have hu0 := List.length_pos_of_ne_nil hu.1
                omega
              let a := wittLongestLyndonPrefix u hu2
              let b := wittLongestLyndonSuffix u hu2
              have hfac := wittStandardFactorization hu hu2
              have huab : u = a ++ b := wittLongestLyndon_append u hu2
              have ha : IsLyndonWord a := hfac.1
              have hb : IsLyndonWord b := hfac.2.1
              have hab : a < b := hfac.2.2
              by_cases hvb : v ≤ b
              · let hw : IsLyndonWord (u ++ v) := (wittLyndon_iff_suffix (u ++ v)).mpr
                  (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
                    ((wittLyndon_iff_suffix v).mp hv) huv)
                have heq := wittLyndonBracket_append K hu hv huv hu2 hvb
                exact heq ▸ wittLyndonBracket_mem_spanFrom K hw rfl le_rfl
              · have hbv : b < v := lt_of_not_ge hvb
                have ha0 := List.length_pos_of_ne_nil ha.1
                have hb0 := List.length_pos_of_ne_nil hb.1
                have hPu : wittLyndonBracket K u hu =
                    ⁅wittLyndonBracket K a ha, wittLyndonBracket K b hb⁆ := by
                  rw [wittLyndonBracket]
                  simp only [dite_eq_right hu1]
                  congr 1
                have hbn : b.length + v.length < n := by
                  have hul := congr_arg List.length huab
                  simp only [List.length_append] at hul
                  omega
                have hbvsp := ih (b.length + v.length) hbn b v hb hv hbv rfl
                have hau : a < u := by
                  rw [huab]
                  exact wittLt_append_self_of_ne_nil a hb.1
                have hav : a < v := hau.trans huv
                have han : a.length + v.length < n := by
                  have hul := congr_arg List.length huab
                  simp only [List.length_append] at hul
                  omega
                have havsp := ih (a.length + v.length) han a v ha hv hav rfl
                have hterm1 :
                    ⁅wittLyndonBracket K a ha,
                      ⁅wittLyndonBracket K b hb, wittLyndonBracket K v hv⁆⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v) := by
                  change ⁅wittLyndonBracket K b hb, wittLyndonBracket K v hv⁆ ∈
                    Submodule.span K {x | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
                      wittWordContent w = wittWordContent (b ++ v) ∧ b ++ v ≤ w ∧
                        x = wittLyndonBracket K w hw} at hbvsp
                  refine Submodule.span_induction (p := fun x _ =>
                    ⁅wittLyndonBracket K a ha, x⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v))
                    ?_ ?_ ?_ ?_ hbvsp
                  · exact by
                      intro x hx
                      rcases hx with ⟨z, hz, hzcontent, hbvz, rfl⟩
                      have haz : a < z := hab.trans_le
                        ((wittLe_append_self b v).trans hbvz)
                      have hzlen : z.length = (b ++ v).length :=
                        wittWordContent_eq_length_eq hzcontent
                      have hazlen : a.length + z.length = n := by
                        have hul := congr_arg List.length huab
                        simp only [List.length_append] at hul hzlen ⊢
                        omega
                      let q : WittLyndonPair r n := ⟨(a, z), ha, hz, haz, hazlen⟩
                      have hle : u ++ v ≤ a ++ z := by
                        rw [huab, List.append_assoc]
                        exact wittAppend_le_append_of_le_of_le le_rfl rfl hbvz
                      have halen : a.length < u.length := by
                        have hul := congr_arg List.length huab
                        simp only [List.length_append] at hul
                        omega
                      have hrel : WittLyndonPairRel q p := by
                        rcases hle.eq_or_lt with heq | hlt
                        · exact Or.inr ⟨heq, halen⟩
                        · exact Or.inl hlt
                      have hrec := rec q hrel
                      have hcontent : wittWordContent (a ++ z) =
                          wittWordContent (u ++ v) := by
                        calc
                          wittWordContent (a ++ z) = wittWordContent (a ++ (b ++ v)) :=
                            wittContent_append_replace hzcontent
                          _ = wittWordContent (u ++ v) := by rw [huab, List.append_assoc]
                      rw [hcontent] at hrec
                      exact wittLyndonSpanFrom_mono K hle hrec
                  · simp
                  · exact by
                      intro x y _ _ hx hy
                      simpa only [lie_add] using Submodule.add_mem _ hx hy
                  · exact by
                      intro c x _ hx
                      simpa only [lie_smul] using Submodule.smul_mem _ c hx
                have hterm2 :
                    ⁅wittLyndonBracket K b hb,
                      ⁅wittLyndonBracket K a ha, wittLyndonBracket K v hv⁆⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v) := by
                  change ⁅wittLyndonBracket K a ha, wittLyndonBracket K v hv⁆ ∈
                    Submodule.span K {x | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
                      wittWordContent w = wittWordContent (a ++ v) ∧ a ++ v ≤ w ∧
                        x = wittLyndonBracket K w hw} at havsp
                  refine Submodule.span_induction (p := fun x _ =>
                    ⁅wittLyndonBracket K b hb, x⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v))
                    ?_ ?_ ?_ ?_ havsp
                  · exact by
                      intro x hx
                      rcases hx with ⟨z, hz, hzcontent, havz, rfl⟩
                      have hzlen : z.length = (a ++ v).length :=
                        wittWordContent_eq_length_eq hzcontent
                      by_cases hbz : b = z
                      · subst z
                        simp
                      · rcases lt_or_gt_of_ne hbz with hbz | hzb
                        · have hbzlen : b.length + z.length = n := by
                            have hul := congr_arg List.length huab
                            simp only [List.length_append] at hul hzlen ⊢
                            omega
                          let q : WittLyndonPair r n := ⟨(b, z), hb, hz, hbz, hbzlen⟩
                          have habSwap := wittLyndon_append_lt_swap ha hb hab
                          have hfirst : (a ++ b) ++ v < (b ++ a) ++ v :=
                            wittAppend_right_lt_of_length_eq habSwap (by
                              simp only [List.length_append]
                              exact Nat.add_comm _ _) v
                          have htail : b ++ (a ++ v) ≤ b ++ z :=
                            wittAppend_le_append_of_le_of_le le_rfl rfl havz
                          have hlt : u ++ v < b ++ z := by
                            calc
                              u ++ v = (a ++ b) ++ v := by rw [huab]
                              _ < (b ++ a) ++ v := hfirst
                              _ = b ++ (a ++ v) := by rw [List.append_assoc]
                              _ ≤ b ++ z := htail
                          have hrel : WittLyndonPairRel q p := Or.inl hlt
                          have hrec := rec q hrel
                          have hcontent : wittWordContent (b ++ z) =
                              wittWordContent (u ++ v) := by
                            rw [huab]
                            simp only [wittWordContent_append]
                            funext i
                            have hzi := congr_fun hzcontent i
                            simp only [wittWordContent_append] at hzi
                            omega
                          rw [hcontent] at hrec
                          exact wittLyndonSpanFrom_mono K hlt.le hrec
                        · have hzbLen : z.length + b.length = n := by
                            have hul := congr_arg List.length huab
                            simp only [List.length_append] at hul hzlen ⊢
                            omega
                          let q : WittLyndonPair r n := ⟨(z, b), hz, hb, hzb, hzbLen⟩
                          have hbvSwap := wittLyndon_append_lt_swap hb hv hbv
                          have hprefix : a ++ (b ++ v) < a ++ (v ++ b) :=
                            (wittAppend_left_lt_iff a (b ++ v) (v ++ b)).mpr hbvSwap
                          have htail : (a ++ v) ++ b ≤ z ++ b :=
                            wittAppend_le_append_of_le_of_le havz hzlen.symm le_rfl
                          have hlt : u ++ v < z ++ b := by
                            calc
                              u ++ v = a ++ (b ++ v) := by rw [huab, List.append_assoc]
                              _ < a ++ (v ++ b) := hprefix
                              _ = (a ++ v) ++ b := by rw [List.append_assoc]
                              _ ≤ z ++ b := htail
                          have hrel : WittLyndonPairRel q p := Or.inl hlt
                          have hrec := rec q hrel
                          have hcontent : wittWordContent (z ++ b) =
                              wittWordContent (u ++ v) := by
                            rw [huab]
                            simp only [wittWordContent_append]
                            funext i
                            have hzi := congr_fun hzcontent i
                            simp only [wittWordContent_append] at hzi
                            omega
                          rw [hcontent] at hrec
                          have hmem := wittLyndonSpanFrom_mono K hlt.le hrec
                          simpa only [lie_skew] using Submodule.neg_mem _ hmem
                  · simp
                  · exact by
                      intro x y _ _ hx hy
                      simpa only [lie_add] using Submodule.add_mem _ hx hy
                  · exact by
                      intro c x _ hx
                      simpa only [lie_smul] using Submodule.smul_mem _ c hx
                rw [hPu, lie_lie]
                exact Submodule.sub_mem _ hterm1 hterm2
      exact hall p0

private theorem wittNil_le {α : Type*} [LinearOrder α] (w : List α) : [] ≤ w := by
  rcases List.lex_nil_or_eq_nil (r := fun a b : α => a < b) w with h | h
  · apply le_of_lt
    exact h
  · exact h ▸ le_rfl

private theorem wittBracket_mem_lyndonSpan (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} (hu : IsLyndonWord u) (hv : IsLyndonWord v) :
    ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ ∈
      wittLyndonSpanFrom K (wittWordContent (u ++ v)) [] := by
  rcases lt_trichotomy u v with huv | huv | huv
  · exact wittLyndonSpanFrom_mono K (wittNil_le (u ++ v))
      (wittOrderedBracket_mem_spanFrom_aux K (u.length + v.length) u v hu hv huv rfl)
  · subst v
    simp
  · have hmem := wittOrderedBracket_mem_spanFrom_aux K (v.length + u.length)
      v u hv hu huv rfl
    rw [← wittContent_swap_append u v] at hmem
    have hmem' := wittLyndonSpanFrom_mono K (wittNil_le (v ++ u)) hmem
    simpa only [lie_skew] using Submodule.neg_mem _ hmem'

private theorem wittLyndonSpan_lie_mem (K : Type) [Field K] {r : ℕ}
    {a b : Fin r → ℕ} {x y : FreeLieAlgebra K (Fin r)}
    (hx : x ∈ wittLyndonSpanFrom K a []) (hy : y ∈ wittLyndonSpanFrom K b []) :
    ⁅x, y⁆ ∈ wittLyndonSpanFrom K (fun i => a i + b i) [] := by
  refine LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (wittLyndonSpanFrom K (fun i => a i + b i) [])
    {z | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
      wittWordContent w = a ∧ [] ≤ w ∧ z = wittLyndonBracket K w hw}
    {z | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
      wittWordContent w = b ∧ [] ≤ w ∧ z = wittLyndonBracket K w hw}
    (LieModule.toEnd K (FreeLieAlgebra K (Fin r))
      (FreeLieAlgebra K (Fin r))).toLinearMap ?_ x y hx hy
  rintro _ ⟨u, hu, hua, _, rfl⟩ _ ⟨v, hv, hvb, _, rfl⟩
  have hmem := wittBracket_mem_lyndonSpan K hu hv
  have hcontent : wittWordContent (u ++ v) = fun i => a i + b i := by
    rw [wittWordContent_append, hua, hvb]
  rw [hcontent] at hmem
  exact hmem

private theorem wittMonomial_mem_lyndonSpan (K : Type) [Field K] {r : ℕ}
    {degree : Fin r → ℕ} {x : FreeLieAlgebra K (Fin r)}
    (hx : IsFreeLieMonomial K degree x) :
    x ∈ wittLyndonSpanFrom K degree [] := by
  induction hx with
  | gen i =>
      let hi : IsLyndonWord [i] :=
        (wittLyndon_iff_suffix [i]).mpr (wittSuffixLyndon_singleton i)
      have hmem := wittLyndonBracket_mem_spanFrom K hi
        (wittWordContent_singleton i) (wittNil_le [i])
      simpa [wittLyndonBracket] using hmem
  | bracket ha hb iha ihb =>
      exact wittLyndonSpan_lie_mem K iha ihb

private theorem wittLyndonSpan_eq_span_range (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) :
    wittLyndonSpanFrom K degree [] =
      Submodule.span K (Set.range (wittLyndonFamily K degree)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, hw, hdegree, _, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨⟨w, hdegree⟩, hw⟩, ?_⟩
    rfl
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact wittLyndonBracket_mem_spanFrom K w.2 w.1.2 (wittNil_le w.1.1)

private theorem wittMultihomogeneousComponent_eq_span (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) :
    freeLieMultihomogeneousComponent K degree =
      Submodule.span K (Set.range (wittLyndonFamily K degree)) := by
  rw [← wittLyndonSpan_eq_span_range K degree]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    exact wittMonomial_mem_lyndonSpan K hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, hdegree, _, rfl⟩
    apply Submodule.subset_span
    rw [← hdegree]
    exact wittLyndonBracket_isMonomial K w hw

/-- **Dimension of a multihomogeneous component of a free Lie algebra.** Let $K$ be a field and
let $n_1, \dots, n_r$ be natural numbers with $n_1 + \dots + n_r > 0$. Then the multihomogeneous
component of multidegree $(n_1, \dots, n_r)$ of the free Lie algebra over $K$ on $r$ generators
has dimension over $K$ equal to Witt's multigraded value $M(n_1, \dots, n_r)$. -/
theorem finrank_freeLieMultihomogeneousComponent
    (K : Type) [Field K] {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    (Module.finrank K (freeLieMultihomogeneousComponent K degree) : ℚ) =
      wittMultigradedValue degree := by
  rw [wittMultihomogeneousComponent_eq_span,
    finrank_span_eq_card (wittLyndonFamily_linearIndependent K degree)]
  exact card_lyndonWordsOfContent_eq_wittMultigradedValue degree hdegree

/-- **Witt's multigraded dimension formula.** Let $K$ be a field, let $r > 0$, and let
$n_1, \dots, n_r$ be natural numbers with $n_1 + \dots + n_r > 0$. Then the multihomogeneous
component of multidegree $(n_1, \dots, n_r)$ of the free Lie algebra over $K$ on $r$ generators
has dimension over $K$ equal to Witt's multigraded value $M(n_1, \dots, n_r)$.

Proof: The Lyndon-word basis identifies the component with the Lyndon words of
the prescribed content, which are counted by Möbius inversion.

Proves `Wanted` entry `witt_multigraded_dimension_formula`.

Source: Pieter Moree, *Convoluted Convolved Fibonacci Numbers*, Journal of
Integer Sequences 7 (2004), Article 04.2.2, Witt's formula paragraph,
lines 621–628,
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Moree/moree12.tex>.
-/
theorem witt_multigraded_dimension_formula
    (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (degree : Fin r → ℕ) (hdegree : 0 < ∑ i, degree i) :
    (Module.finrank K (freeLieMultihomogeneousComponent K degree) : ℚ) =
      wittMultigradedValue degree :=
  finrank_freeLieMultihomogeneousComponent K degree hdegree

end MetaMathlibExt

end
