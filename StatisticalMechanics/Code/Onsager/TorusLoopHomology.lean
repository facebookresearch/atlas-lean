/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.DecorationSum
import Code.Onsager.TorusLoopCharacter








namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_xWrap {L : ℕ} (d : ons_Dart L) : Prop :=
  (d.2 = 0 ∧ d.1.1 = -1) ∨ (d.2 = 2 ∧ d.1.1 = 0)

def ons_yWrap {L : ℕ} (d : ons_Dart L) : Prop :=
  (d.2 = 1 ∧ d.1.2 = -1) ∨ (d.2 = 3 ∧ d.1.2 = 0)

instance {L : ℕ} (d : ons_Dart L) : Decidable (ons_xWrap d) := by
  unfold ons_xWrap
  infer_instance

instance {L : ℕ} (d : ons_Dart L) : Decidable (ons_yWrap d) := by
  unfold ons_yWrap
  infer_instance

def ons_xWrapSign {L : ℕ} (d : ons_Dart L) : ℤ :=
  if d.2 = 0 ∧ d.1.1 = -1 then 1
  else if d.2 = 2 ∧ d.1.1 = 0 then -1 else 0

def ons_yWrapSign {L : ℕ} (d : ons_Dart L) : ℤ :=
  if d.2 = 1 ∧ d.1.2 = -1 then 1
  else if d.2 = 3 ∧ d.1.2 = 0 then -1 else 0

theorem ons_zmod_val_neg_one (L : ℕ) [NeZero L] :
    (-1 : ZMod L).val = L - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  rw [ZMod.val_neg_one]
  omega

theorem ons_dirExponentX_eq_val_diff_add_wrap
    {L : ℕ} [Fact (2 < L)] (d : ons_Dart L) :
    ons_dirExponentX d.2 =
      (((ons_dirStep L d.2 d.1).1.val : ℕ) : ℤ) -
        ((d.1.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign d := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  rcases d with ⟨p, mu⟩
  fin_cases mu
  · change (1 : ℤ) = (((p.1 + 1).val : ℕ) : ℤ) -
      ((p.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign (p, 0)
    by_cases hp : p.1 = -1
    · have hv : p.1.val = L - 1 := by rw [hp, ons_zmod_val_neg_one]
      have hh : (p.1 + 1).val = 0 := by rw [hp]; simp
      rw [hv, hh]
      simp [ons_xWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hv : p.1.val + 1 < L := by
        have hlt := ZMod.val_lt p.1
        have hne : p.1.val ≠ L - 1 := by
          intro h
          apply hp
          apply ZMod.val_injective
          rw [h, ons_zmod_val_neg_one]
        omega
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
      simp [ons_xWrapSign, hp]
  · simp [ons_dirExponentX, ons_dirStep, ons_xWrapSign]
  · change (-1 : ℤ) = (((p.1 - 1).val : ℕ) : ℤ) -
      ((p.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign (p, 2)
    by_cases hp : p.1 = 0
    · have hv : p.1.val = 0 := by rw [hp]; exact ZMod.val_zero
      have hh : (p.1 - 1).val = L - 1 := by
        rw [hp, zero_sub, ons_zmod_val_neg_one]
      rw [hv, hh]
      simp [ons_xWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hpval : p.1.val ≠ 0 := by
        intro h
        apply hp
        exact (ZMod.val_eq_zero p.1).mp h
      have hone : (1 : ZMod L).val ≤ p.1.val := by
        rw [ZMod.val_one]
        omega
      rw [ZMod.val_sub hone, ZMod.val_one]
      simp [ons_xWrapSign, hp]
  · simp [ons_dirExponentX, ons_dirStep, ons_xWrapSign]

theorem ons_dirExponentY_eq_val_diff_add_wrap
    {L : ℕ} [Fact (2 < L)] (d : ons_Dart L) :
    ons_dirExponentY d.2 =
      (((ons_dirStep L d.2 d.1).2.val : ℕ) : ℤ) -
        ((d.1.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign d := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  rcases d with ⟨p, mu⟩
  fin_cases mu
  · simp [ons_dirExponentY, ons_dirStep, ons_yWrapSign]
  · change (1 : ℤ) = (((p.2 + 1).val : ℕ) : ℤ) -
      ((p.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign (p, 1)
    by_cases hp : p.2 = -1
    · have hv : p.2.val = L - 1 := by rw [hp, ons_zmod_val_neg_one]
      have hh : (p.2 + 1).val = 0 := by rw [hp]; simp
      rw [hv, hh]
      simp [ons_yWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hv : p.2.val + 1 < L := by
        have hlt := ZMod.val_lt p.2
        have hne : p.2.val ≠ L - 1 := by
          intro h
          apply hp
          apply ZMod.val_injective
          rw [h, ons_zmod_val_neg_one]
        omega
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
      simp [ons_yWrapSign, hp]
  · simp [ons_dirExponentY, ons_dirStep, ons_yWrapSign]
  · change (-1 : ℤ) = (((p.2 - 1).val : ℕ) : ℤ) -
      ((p.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign (p, 3)
    by_cases hp : p.2 = 0
    · have hv : p.2.val = 0 := by rw [hp]; exact ZMod.val_zero
      have hh : (p.2 - 1).val = L - 1 := by
        rw [hp, zero_sub, ons_zmod_val_neg_one]
      rw [hv, hh]
      simp [ons_yWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hpval : p.2.val ≠ 0 := by
        intro h
        apply hp
        exact (ZMod.val_eq_zero p.2).mp h
      have hone : (1 : ZMod L).val ≤ p.2.val := by
        rw [ZMod.val_one]
        omega
      rw [ZMod.val_sub hone, ZMod.val_one]
      simp [ons_yWrapSign, hp]

theorem ons_sum_dirExponentX_eq_wrap
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (∑ k, ons_dirExponentX (d k).2) =
      (L : ℤ) * ∑ k, ons_xWrapSign (d k) := by
  have hhead :
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ))) =
        ∑ k, (((d k).1.1.val : ℕ) : ℤ) := by
    calc
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ))) =
          ∑ k, (((d (k - 1)).1.1.val : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : k - 1 + 1 = k := by abel
        have h := hvalid (k - 1)
        rw [hk] at h
        rw [h]
      _ = ∑ k, (((d k).1.1.val : ℕ) : ℤ) :=
        by simpa [sub_eq_add_neg] using
          (Equiv.sum_comp (Equiv.addRight (-1 : Fin n))
            (fun k => (((d k).1.1.val : ℕ) : ℤ)))
  calc
    (∑ k, ons_dirExponentX (d k).2) =
        ∑ k, ((((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ) -
          (((d k).1.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign (d k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact ons_dirExponentX_eq_val_diff_add_wrap (d k)
    _ = ((∑ k, (((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ)) -
          ∑ k, (((d k).1.1.val : ℕ) : ℤ)) +
        ∑ k, (L : ℤ) * ons_xWrapSign (d k) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (L : ℤ) * ∑ k, ons_xWrapSign (d k) := by
      rw [hhead, sub_self, zero_add, Finset.mul_sum]

theorem ons_sum_dirExponentY_eq_wrap
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (∑ k, ons_dirExponentY (d k).2) =
      (L : ℤ) * ∑ k, ons_yWrapSign (d k) := by
  have hhead :
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ))) =
        ∑ k, (((d k).1.2.val : ℕ) : ℤ) := by
    calc
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ))) =
          ∑ k, (((d (k - 1)).1.2.val : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : k - 1 + 1 = k := by abel
        have h := hvalid (k - 1)
        rw [hk] at h
        rw [h]
      _ = ∑ k, (((d k).1.2.val : ℕ) : ℤ) :=
        by simpa [sub_eq_add_neg] using
          (Equiv.sum_comp (Equiv.addRight (-1 : Fin n))
            (fun k => (((d k).1.2.val : ℕ) : ℤ)))
  calc
    (∑ k, ons_dirExponentY (d k).2) =
        ∑ k, ((((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ) -
          (((d k).1.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign (d k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact ons_dirExponentY_eq_val_diff_add_wrap (d k)
    _ = ((∑ k, (((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ)) -
          ∑ k, (((d k).1.2.val : ℕ) : ℤ)) +
        ∑ k, (L : ℤ) * ons_yWrapSign (d k) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (L : ℤ) * ∑ k, ons_yWrapSign (d k) := by
      rw [hhead, sub_self, zero_add, Finset.mul_sum]

private theorem ons_two_ne_zero {L : ℕ} [Fact (2 < L)] :
    (2 : ZMod L) ≠ 0 := by
  rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have := (Fact.out : 2 < L)
  omega

theorem ons_xSeamEdge_portEdge_iff {L : ℕ} [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_xSeamEdge L (ons_portEdge L d) ↔ ons_xWrap d := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp only [ons_xWrap] <;> norm_num <;> simp
  · exact show ons_xSeamEdge L (ons_portEdge L (p, 0)) ↔ p.1 = -1 from by
      simp only [ons_xSeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨y, (⟨hp, hstep, -⟩ | ⟨hp, -, -⟩)⟩
        · have hx : p.1 = 0 := congrArg Prod.fst hp
          rw [hx] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination hstep
        · simpa using congrArg Prod.fst hp
      · intro hp
        refine ⟨p.2, Or.inr ⟨Prod.ext hp rfl, ?_, rfl⟩⟩
        rw [hp]
        simp
  · exact show ¬ons_xSeamEdge L (ons_portEdge L (p, 1)) from by
      rintro ⟨y, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, hm, -⟩ | ⟨hp, h0, -⟩)
      · have h0' : p.1 = 0 := congrArg Prod.fst hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.1 = -1 := congrArg Prod.fst hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
  · exact show ons_xSeamEdge L (ons_portEdge L (p, 2)) ↔ p.1 = 0 from by
      simp only [ons_xSeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨y, (⟨hp, -, -⟩ | ⟨hp, hstep, -⟩)⟩
        · simpa using congrArg Prod.fst hp
        · have hx : p.1 = -1 := congrArg Prod.fst hp
          rw [hx] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination -hstep
      · intro hp
        refine ⟨p.2, Or.inl ⟨Prod.ext hp rfl, ?_, rfl⟩⟩
        rw [hp]
        simp
  · exact show ¬ons_xSeamEdge L (ons_portEdge L (p, 3)) from by
      rintro ⟨y, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, hm, -⟩ | ⟨hp, h0, -⟩)
      · have h0' : p.1 = 0 := congrArg Prod.fst hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.1 = -1 := congrArg Prod.fst hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1

theorem ons_ySeamEdge_portEdge_iff {L : ℕ} [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_ySeamEdge L (ons_portEdge L d) ↔ ons_yWrap d := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp only [ons_yWrap] <;> norm_num <;> simp
  · exact show ¬ons_ySeamEdge L (ons_portEdge L (p, 0)) from by
      rintro ⟨x, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, -, hm⟩ | ⟨hp, -, h0⟩)
      · have h0' : p.2 = 0 := congrArg Prod.snd hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.2 = -1 := congrArg Prod.snd hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
  · exact show ons_ySeamEdge L (ons_portEdge L (p, 1)) ↔ p.2 = -1 from by
      simp only [ons_ySeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨x, (⟨hp, -, hstep⟩ | ⟨hp, -, -⟩)⟩
        · have hy : p.2 = 0 := congrArg Prod.snd hp
          rw [hy] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination hstep
        · simpa using congrArg Prod.snd hp
      · intro hp
        refine ⟨p.1, Or.inr ⟨Prod.ext rfl hp, rfl, ?_⟩⟩
        rw [hp]
        simp
  · exact show ¬ons_ySeamEdge L (ons_portEdge L (p, 2)) from by
      rintro ⟨x, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, -, hm⟩ | ⟨hp, -, h0⟩)
      · have h0' : p.2 = 0 := congrArg Prod.snd hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.2 = -1 := congrArg Prod.snd hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
  · exact show ons_ySeamEdge L (ons_portEdge L (p, 3)) ↔ p.2 = 0 from by
      simp only [ons_ySeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨x, (⟨hp, -, -⟩ | ⟨hp, -, hstep⟩)⟩
        · simpa using congrArg Prod.snd hp
        · have hy : p.2 = -1 := congrArg Prod.snd hp
          rw [hy] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination -hstep
      · intro hp
        refine ⟨p.1, Or.inl ⟨Prod.ext rfl hp, rfl, ?_⟩⟩
        rw [hp]
        simp

noncomputable instance ons_xSeamEdge_decidable {L : ℕ}
    (e : Sym2 (ZMod L × ZMod L)) : Decidable (ons_xSeamEdge L e) :=
  Classical.propDecidable _

noncomputable instance ons_ySeamEdge_decidable {L : ℕ}
    (e : Sym2 (ZMod L × ZMod L)) : Decidable (ons_ySeamEdge L e) :=
  Classical.propDecidable _


noncomputable def ons_dartEdgeSet {L n : ℕ}
    (d : Fin n → ons_Dart L) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  Finset.univ.image (fun k => ons_portEdge L (d k))

theorem ons_portEdge_loop_injective {L n : ℕ}
    [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    Function.Injective (fun k => ons_portEdge L (d k)) := by
  intro i j hij
  rcases (ons_portEdge_eq_iff L (d j) (d i)).mp hij with hsame | hrev
  · exact hsite (congrArg Prod.fst hsame)
  · have hj : j - 1 + 1 = j := by abel
    have hsites : (d i).1 = (d (j - 1)).1 := by
      calc
        (d i).1 = (ons_dartRev L (d j)).1 := congrArg Prod.fst hrev
        _ = ons_dirStep L (d j).2 (d j).1 := rfl
        _ = (d (j - 1)).1 := by
          have h := hvalid (j - 1)
          rw [hj] at h
          exact h.symm
    have hi : i = j - 1 := hsite hsites
    have hdir := congrArg Prod.snd hrev
    subst i
    exfalso
    apply (hnu (j - 1))
    rw [hj]
    simpa only [ons_dartRev] using hdir

theorem ons_dartEdgeSet_filter_x {L n : ℕ} [Fact (2 < L)]
    (d : Fin n → ons_Dart L) :
    (ons_dartEdgeSet d).filter (ons_xSeamEdge L) =
      (Finset.univ.filter (fun k => ons_xWrap (d k))).image
        (fun k => ons_portEdge L (d k)) := by
  classical
  ext edge
  simp only [ons_dartEdgeSet, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, hk⟩, hseam⟩
    refine ⟨k, ?_, hk⟩
    rw [← hk] at hseam
    exact (ons_xSeamEdge_portEdge_iff (d k)).mp hseam
  · rintro ⟨k, hwrap, hk⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← hk]
    exact (ons_xSeamEdge_portEdge_iff (d k)).mpr hwrap

theorem ons_dartEdgeSet_filter_y {L n : ℕ} [Fact (2 < L)]
    (d : Fin n → ons_Dart L) :
    (ons_dartEdgeSet d).filter (ons_ySeamEdge L) =
      (Finset.univ.filter (fun k => ons_yWrap (d k))).image
        (fun k => ons_portEdge L (d k)) := by
  classical
  ext edge
  simp only [ons_dartEdgeSet, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, hk⟩, hseam⟩
    refine ⟨k, ?_, hk⟩
    rw [← hk] at hseam
    exact (ons_ySeamEdge_portEdge_iff (d k)).mp hseam
  · rintro ⟨k, hwrap, hk⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← hk]
    exact (ons_ySeamEdge_portEdge_iff (d k)).mpr hwrap

theorem ons_dartEdgeSet_xSeam_card {L n : ℕ}
    [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    ((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card =
      (Finset.univ.filter (fun k => ons_xWrap (d k))).card := by
  rw [ons_dartEdgeSet_filter_x]
  exact Finset.card_image_iff.mpr
    ((ons_portEdge_loop_injective d hvalid hsite hnu).injOn)

theorem ons_dartEdgeSet_ySeam_card {L n : ℕ}
    [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    ((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card =
      (Finset.univ.filter (fun k => ons_yWrap (d k))).card := by
  rw [ons_dartEdgeSet_filter_y]
  exact Finset.card_image_iff.mpr
    ((ons_portEdge_loop_injective d hvalid hsite hnu).injOn)

theorem ons_intParity_eq_zmod (m : ℤ) :
    ons_intParity m = (m : ZMod 2) := by
  apply Fin.ext
  by_cases hm : Even m
  · simp only [ons_intParity, if_pos hm, Fin.val_zero]
    have hz : (m : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact even_iff_two_dvd.mp hm
    have hv := congrArg ZMod.val hz
    simpa using hv.symm
  · have ho := Int.not_even_iff_odd.mp hm
    simp only [ons_intParity, if_neg hm, Fin.val_one]
    rcases ho with ⟨k, rfl⟩
    have htwo : (2 : ZMod 2) = 0 := by decide
    have hz : (((2 * k + 1 : ℤ) : ZMod 2)) = 1 := by
      push_cast
      rw [htwo, zero_mul, zero_add]
    have hv := congrArg ZMod.val hz
    simpa using hv.symm

theorem ons_xWrapSign_cast (d : ons_Dart L) :
    ((ons_xWrapSign d : ℤ) : ZMod 2) =
      if ons_xWrap d then 1 else 0 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_xWrapSign, ons_xWrap]

theorem ons_yWrapSign_cast (d : ons_Dart L) :
    ((ons_yWrapSign d : ℤ) : ZMod 2) =
      if ons_yWrap d then 1 else 0 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_yWrapSign, ons_yWrap]

theorem ons_intParity_sum_xWrapSign {L n : ℕ}
    (d : Fin n → ons_Dart L) :
    ons_intParity (∑ k, ons_xWrapSign (d k)) =
      ⟨(Finset.univ.filter (fun k => ons_xWrap (d k))).card % 2,
        Nat.mod_lt _ (by decide)⟩ := by
  rw [ons_intParity_eq_zmod]
  apply Fin.ext
  rw [Int.cast_sum]
  simp_rw [ons_xWrapSign_cast]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ZMod.val_natCast 2 _

theorem ons_intParity_sum_yWrapSign {L n : ℕ}
    (d : Fin n → ons_Dart L) :
    ons_intParity (∑ k, ons_yWrapSign (d k)) =
      ⟨(Finset.univ.filter (fun k => ons_yWrap (d k))).card % 2,
        Nat.mod_lt _ (by decide)⟩ := by
  rw [ons_intParity_eq_zmod]
  apply Fin.ext
  rw [Int.cast_sum]
  simp_rw [ons_yWrapSign_cast]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ZMod.val_natCast 2 _



theorem ons_evenHomology_dartEdgeSet_eq_windingParity
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
    (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my) :
    ons_evenHomology L (ons_dartEdgeSet d) =
      ons_windingParity mx my := by
  have hL : (L : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
      (Fact.out : 2 < L)))
  have hxwrap := ons_sum_dirExponentX_eq_wrap d hvalid
  have hywrap := ons_sum_dirExponentY_eq_wrap d hvalid
  have hx : mx = ∑ k, ons_xWrapSign (d k) := by
    apply mul_left_cancel₀ hL
    exact hmx.symm.trans hxwrap
  have hy : my = ∑ k, ons_yWrapSign (d k) := by
    apply mul_left_cancel₀ hL
    exact hmy.symm.trans hywrap
  apply Prod.ext
  · change
      ⟨((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card % 2,
          Nat.mod_lt _ (by decide)⟩ = ons_intParity mx
    rw [ons_dartEdgeSet_xSeam_card d hvalid hsite hnu, hx]
    exact (ons_intParity_sum_xWrapSign d).symm
  · change
      ⟨((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card % 2,
          Nat.mod_lt _ (by decide)⟩ = ons_intParity my
    rw [ons_dartEdgeSet_ySeam_card d hvalid hsite hnu, hy]
    exact (ons_intParity_sum_yWrapSign d).symm

theorem ons_dartEdgeSet_card {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    (ons_dartEdgeSet d).card = n := by
  rw [ons_dartEdgeSet, Finset.card_image_iff.mpr
    ((ons_portEdge_loop_injective d hvalid hsite hnu).injOn),
    Finset.card_univ, Fintype.card_fin]



theorem ons_loopWeight_spinPhase_eq_homology
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (x omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      ons_spinLinearCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) *
        ons_loopWeight (ons_KWmat L x omega) d := by
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists d hvalid
  rw [ons_loopWeight_spinPhase_of_winding x omega a b d mx my hmx hmy,
    ons_spinPhase_character]
  rw [ons_evenHomology_dartEdgeSet_eq_windingParity
    d hvalid hsite hnu mx my hmx hmy]



theorem ons_loopWeight_spinPhase_eq_spinCharacter
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (x omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
    (hgeom : ons_loopWeight (ons_KWmat L x omega) d =
      -(ons_spinCharacter 0 0
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n := by
  rw [ons_loopWeight_spinPhase_eq_homology
    x omega a b d hvalid hsite hnu, hgeom]
  have hchar := ons_spinLinear_mul_quadratic a b
    (ons_evenHomology L (ons_dartEdgeSet d))
  calc
    ons_spinLinearCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) *
        (-(ons_spinCharacter 0 0
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n) =
      -(ons_spinLinearCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) *
        (ons_spinCharacter 0 0
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ)) * x ^ n := by ring
    _ = -(ons_spinCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n := by
      rw [hchar]

end StatMech.Onsager
