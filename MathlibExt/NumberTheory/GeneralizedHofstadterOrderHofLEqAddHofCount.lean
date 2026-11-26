/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`WordGrowth.v` (hofstadter_g, https://github.com/letouzey/hofstadter_g):
the definitions `LBound` and `SteinerThm` and the lemmas `steiner_thm_disj`,
`steiner_thm_corestep`, `steiner_thm` and `LBound_unique`, adapted here as `LBound_aux`,
`SteinerThm_aux`, `steiner_disj_aux`, `steiner_corestep_aux` with its case lemmas,
`steiner_all_aux` and `lbound_unique_aux`.
Public-domain dedication (https://github.com/letouzey/hofstadter_g/blob/main/LICENSE):
"I, Pierre Letouzey, waive my copyright over this Coq development,
and place it into the Public Domain".
Authors: Pierre Letouzey
-/

module

public import MathlibExt.NumberTheory.GeneralizedHofstadterOrder
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The image length `L_k` as a letter count

This module proves that the image length `L_k(n) = |τ_k(x_k[0:n))|` equals `n` plus the
number of letters `k` in the prefix, and `n` plus the `(k-1)`-fold iterate of `F_k`
(`hofL_eq_add_hofCount`).

Statements from Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3
(arXiv:2410.00529; TeX source read for the definitions).
-/

namespace MetaMathlibExt

open hofCount_one_succ_le

private theorem hofCount_one_eq (n : ℕ) : hofCount 1 (· = 1) n = n := by
  rw [hofCount]
  refine Eq.trans ?_ (prefix_length 1 n)
  apply List.countP_eq_length.mpr
  intro a ha
  rw [hofPrefix_eq_map] at ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  have hmem := letter_bounds (k := 1) le_rfl i
  simp only [decide_eq_true_eq]
  omega

private theorem hofstadterF_le_aux (k n : ℕ) : hofstadterF k n ≤ n := by
  unfold hofstadterF
  exact hofstadterFAux_le k n n

private theorem iterate_le_aux (k j n : ℕ) : (hofstadterF k)^[j] n ≤ n := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (hofstadterF_le_aux k _).trans ih

private theorem iterate_zero_eq_aux (k j : ℕ) : (hofstadterF k)^[j] 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

private theorem hofstadterF_one_aux (k : ℕ) : hofstadterF k 1 = 1 := by
  have h := hofstadterF_eq k (show 1 ≤ 1 by omega)
  have h11 : (1 : ℕ) - 1 = 0 := rfl
  rw [h11, iterate_zero_eq_aux] at h
  omega

private theorem hofstadterF_succ_eq (k n : ℕ) :
    hofstadterF k (n + 1) = (n + 1) - (hofstadterF k)^[k] n := by
  have h := hofstadterF_eq k (show 1 ≤ n + 1 by omega)
  have hsub : (n + 1) - 1 = n := by omega
  rw [hsub] at h
  exact h

private theorem hofstadterF_step_aux (k n : ℕ) :
    hofstadterF k (n + 1) = hofstadterF k n ∨
      hofstadterF k (n + 1) = hofstadterF k n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [hofstadterF_zero, hofstadterF_one_aux]
      right
      rfl
    | succ n =>
      have inner : ∀ p m, m ≤ n →
          (hofstadterF k)^[p] (m + 1) = (hofstadterF k)^[p] m ∨
            (hofstadterF k)^[p] (m + 1) = (hofstadterF k)^[p] m + 1 := by
        intro p
        induction p with
        | zero =>
          intro m _
          right
          rfl
        | succ p ihp =>
          intro m hm
          have hcases := ihp m hm
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          rcases hcases with h | h
          · left
            rw [h]
          · have hlt : (hofstadterF k)^[p] m < n + 1 := by
              have hle := iterate_le_aux k p m
              omega
            have hstep := ih _ hlt
            rw [h]
            exact hstep
      have hkk := inner k n (Nat.le_refl _)
      rw [hofstadterF_succ_eq k (n + 1), hofstadterF_succ_eq k n]
      have hle1 := iterate_le_aux k k (n + 1)
      have hle2 := iterate_le_aux k k n
      omega

private theorem iterate_step_aux (k p n : ℕ) :
    (hofstadterF k)^[p] (n + 1) = (hofstadterF k)^[p] n ∨
      (hofstadterF k)^[p] (n + 1) = (hofstadterF k)^[p] n + 1 := by
  induction p with
  | zero => right; rfl
  | succ p ihp =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rcases ihp with h | h
    · left; rw [h]
    · have hstep := hofstadterF_step_aux k ((hofstadterF k)^[p] n)
      rw [h]
      exact hstep

private theorem hofstadterF_mono_succ_aux (k n : ℕ) :
    hofstadterF k n ≤ hofstadterF k (n + 1) := by
  rcases hofstadterF_step_aux k n with h | h <;> omega

private theorem hofstadterF_mono_aux (k n m : ℕ) (h : n ≤ m) :
    hofstadterF k n ≤ hofstadterF k m := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact ih.trans (hofstadterF_mono_succ_aux k _)

private theorem hofstadterF_nonzero_aux (k n : ℕ) (hn : 0 < n) :
    0 < hofstadterF k n := by
  have h1 := hofstadterF_one_aux k
  have hmono := hofstadterF_mono_aux k 1 n (by omega)
  omega

private theorem iterate_nonzero_aux (k p n : ℕ) (hn : 0 < n) :
    0 < (hofstadterF k)^[p] n := by
  induction p with
  | zero => simpa using hn
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    exact hofstadterF_nonzero_aux k _ ih

private theorem iterate_eq_zero_inv_aux (k p n : ℕ)
    (h : (hofstadterF k)^[p] n = 0) : n = 0 := by
  by_contra hn
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have := iterate_nonzero_aux k p n hpos
  omega

private theorem iterate_one_eq_aux (k j : ℕ) : (hofstadterF k)^[j] 1 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    exact hofstadterF_one_aux k

private theorem hofstadterF_two_aux (k : ℕ) : hofstadterF k 2 = 1 := by
  have h := hofstadterF_succ_eq k 1
  rw [iterate_one_eq_aux] at h
  omega

private theorem hofstadterF_eqn_add_aux (k n : ℕ) :
    hofstadterF k (n + 1) + (hofstadterF k)^[k] n = n + 1 := by
  rw [hofstadterF_succ_eq]
  have hle := iterate_le_aux k k n
  omega

private theorem hofstadterF_fix_aux (k n : ℕ) :
    hofstadterF k n = n ↔ n ≤ 1 := by
  constructor
  · intro h
    cases n with
    | zero => omega
    | succ n =>
      have hadd := hofstadterF_eqn_add_aux k n
      rw [h] at hadd
      have h0 : (hofstadterF k)^[k] n = 0 := by omega
      have hn0 := iterate_eq_zero_inv_aux k k n h0
      omega
  · intro h
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => exact hofstadterF_one_aux k
      | succ n => omega

private theorem hofstadterF_lt_aux (k n : ℕ) (hn : 1 < n) :
    hofstadterF k n < n := by
  have hle := hofstadterF_le_aux k n
  have hfix := hofstadterF_fix_aux k n
  omega

private theorem image_add_aux (k a b n : ℕ) :
    imageLength k (a + b) n = imageLength k a (imageLength k b n) := by
  have h : (hofTauList k)^[b] (hofPrefix k n) = hofPrefix k (imageLength k b n) :=
    iterate_prefix
  change ((hofTauList k)^[a + b] (hofPrefix k n)).length = _
  rw [Function.iterate_add_apply, h]
  rfl


private def LBound_aux (k j n m : ℕ) : Prop :=
  imageLength k j (m - 1) < n ∧ n ≤ imageLength k j m

private theorem block_one_eq (k a : ℕ) :
    (hofTauList k)^[1] [a] = hofTau k a := by
  rw [Function.iterate_succ_apply']
  simp [hofTauList]

private theorem steiner_disj_aux {k n : ℕ} (hn : 1 ≤ n)
    (h : LBound_aux k 1 n (hofstadterF k n)) :
    imageLength k 1 (hofstadterF k n) = n ∨ hofWord k n = 1 := by
  have hFpos : 1 ≤ hofstadterF k n := hofstadterF_nonzero_aux k n (by omega)
  obtain ⟨t, ht⟩ : ∃ t, hofstadterF k n = t + 1 := ⟨hofstadterF k n - 1, by omega⟩
  rw [ht] at h ⊢
  simp only [LBound_aux, Nat.add_sub_cancel] at h
  rw [image_succ] at h
  -- h : L(t) < n ∧ n ≤ L(t) + |block t|, where block t = tau^1([x[t]])
  have hblock := block_one_eq k (hofWord k t)
  by_cases hx : hofWord k t = k
  · -- block is [k, 1], length 2
    rw [hblock] at h
    simp only [hofTau, hx, ↓reduceIte, List.length_cons, List.length_cons,
      List.length_nil] at h
    have hL : imageLength k 1 (t + 1) = imageLength k 1 t + 2 := by
      rw [image_succ, hblock]
      simp [hofTau, hx]
    -- h : L(t) < n ∧ n ≤ L(t) + 2
    by_cases heq : imageLength k 1 (t + 1) = n
    · left; exact heq
    · right
      have hn_eq : n = imageLength k 1 t + 1 := by omega
      have hprefix := prefix_image_succ k 1 t
      rw [hblock, hx] at hprefix
      simp only [hofTau, ↓reduceIte] at hprefix
      have he' := congrArg (fun w : List ℕ => w[imageLength k 1 t + 1]?) hprefix
      simpa [hofPrefix_eq_map, List.getElem?_append_right, show
        imageLength k 1 t + 1 < imageLength k 1 (t + 1) by omega,
        hn_eq] using he'
  · -- block is [a+1], length 1
    rw [hblock] at h
    simp only [hofTau, hx, ↓reduceIte, List.length_cons, List.length_nil] at h
    have hL : imageLength k 1 (t + 1) = imageLength k 1 t + 1 := by
      rw [image_succ, hblock]
      simp [hofTau, hx]
    left
    omega

private def SteinerThm_aux (k j n : ℕ) : Prop :=
  0 < n → LBound_aux k j n ((hofstadterF k)^[j] n)

private theorem steiner_corestep_flat_eq {k n : ℕ} (hn : 2 ≤ n)
    (E : (hofstadterF k)^[k] n = (hofstadterF k)^[k] (n - 1))
    (EQ : imageLength k 1 (hofstadterF k n) = n) :
    LBound_aux k 1 (n + 1) (hofstadterF k (n + 1)) := by
  have hFn : hofstadterF k n = n - (hofstadterF k)^[k] (n - 1) := by
    have hs := hofstadterF_succ_eq k (n - 1)
    rw [show (n - 1) + 1 = n by omega] at hs
    exact hs
  have hFS : hofstadterF k (n + 1) = hofstadterF k n + 1 := by
    rw [hofstadterF_succ_eq k n, hFn, E]
    have hle := iterate_le_aux k k (n - 1)
    omega
  have hL1 : imageLength k 1 (hofstadterF k (n + 1) - 1) = n := by
    have hsub : hofstadterF k (n + 1) - 1 = hofstadterF k n := by omega
    rw [hsub, EQ]
  have hL2 : n + 1 ≤ imageLength k 1 (hofstadterF k (n + 1)) := by
    rw [hFS, image_succ, EQ]
    have hlen : 1 ≤ ((hofTauList k)^[1] [hofWord k (hofstadterF k n)]).length := by
      rw [block_one_eq]
      exact one_le_length_hofTau k _
    omega
  simp only [LBound_aux, hL1]
  constructor
  · omega
  · exact hL2

private theorem word_at_image_k_aux {k p : ℕ} (hk : 1 ≤ k) :
    hofWord k (imageLength k k p) = k := by
  have ha := (letter_bounds hk p).2
  have hblock := iterate_letter ha (le_refl k) (by omega : k ≤ hofWord k p + k)
  exact word_at_image hblock

private theorem block_getElem_q_aux2 (k a i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ a) :
    (k :: List.range' 1 a)[i]? = some i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_range' (by omega : j < a)]
  congr 1
  omega

private theorem steiner_exfalso_aux {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (E : (hofstadterF k)^[k] n = (hofstadterF k)^[k] (n - 1))
    (EQ2 : hofWord k n = 1)
    (IHn : LBound_aux k k n ((hofstadterF k)^[k] n))
    (IHn1 : LBound_aux k k (n - 1) ((hofstadterF k)^[k] (n - 1))) :
    False := by
  have hm_pos : 1 ≤ (hofstadterF k)^[k] n := iterate_nonzero_aux k k n (by omega)
  obtain ⟨t, ht⟩ : ∃ t, (hofstadterF k)^[k] n = t + 1 :=
    ⟨(hofstadterF k)^[k] n - 1, by omega⟩
  have ht2 : (hofstadterF k)^[k] (n - 1) = t + 1 := by omega
  rw [ht] at IHn
  rw [ht2] at IHn1
  simp only [LBound_aux, Nat.add_sub_cancel] at IHn IHn1
  by_cases heq : n = imageLength k k (t + 1)
  · have hx : hofWord k n = k := by
      rw [heq]
      exact word_at_image_k_aux (by omega : 1 ≤ k)
    omega
  · have hlt : n < imageLength k k (t + 1) := by omega
    have ha_le := (letter_bounds (by omega : 1 ≤ k) t).2
    have ha_ge := (letter_bounds (by omega : 1 ≤ k) t).1
    have hblock := iterate_letter ha_le (le_refl k) (by omega : k ≤ hofWord k t + k)
    have harith : hofWord k t + k - k = hofWord k t := by omega
    rw [harith] at hblock
    have hprefix := prefix_image_succ k k t
    rw [hblock] at hprefix
    have hL : imageLength k k (t + 1) = imageLength k k t + (hofWord k t + 1) := by
      rw [image_succ, hblock]
      simp
    have hoff_ge : 2 ≤ n - imageLength k k t := by omega
    have hoff_le : n - imageLength k k t ≤ hofWord k t := by omega
    have hle : imageLength k k t ≤ n := by omega
    have hq := block_getElem_q_aux2 k (hofWord k t) (n - imageLength k k t)
      (by omega) hoff_le
    have hcontra : 1 = n - imageLength k k t := by
      have he' := congrArg (fun w : List ℕ => w[n]?) hprefix
      simpa [hofPrefix_eq_map, List.getElem?_append_right, hlt, hle, hq, EQ2] using he'
    omega

private theorem iterate_succ_right_general (f : ℕ → ℕ) (k n : ℕ) (hk : 1 ≤ k) :
    f^[k] n = f^[k - 1] (f n) := by
  have hk_eq : k = (k - 1) + 1 := by omega
  nth_rewrite 1 [hk_eq]
  rw [Function.iterate_succ_apply]

private theorem iterate_succ_right_aux (k n : ℕ) (hk : 1 ≤ k) :
    (hofstadterF k)^[k] n = (hofstadterF k)^[k - 1] (hofstadterF k n) :=
  iterate_succ_right_general _ _ _ hk

private theorem steiner_step_E_aux {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (E : (hofstadterF k)^[k] n = (hofstadterF k)^[k] (n - 1) + 1) :
    hofstadterF k n = hofstadterF k (n - 1) + 1 := by
  have hstep := hofstadterF_step_aux k (n - 1)
  have hn_eq : (n - 1) + 1 = n := by omega
  rw [hn_eq] at hstep
  rcases hstep with h | h
  · exfalso
    have h1 := iterate_succ_right_aux k n (by omega)
    have h2 := iterate_succ_right_aux k (n - 1) (by omega)
    rw [h1, h2, h] at E
    omega
  · exact h

private theorem steiner_step_H_aux {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (E : (hofstadterF k)^[k] n = (hofstadterF k)^[k] (n - 1) + 1)
    (HL' : imageLength k k ((hofstadterF k)^[k] (n - 1)) = n - 1) :
    hofWord k (n - 1) = k ∧ hofWord k n = 1 := by
  have hm_pos : 1 ≤ (hofstadterF k)^[k] (n - 1) :=
    iterate_nonzero_aux k k (n - 1) (by omega)
  -- m' = F^k(n-1), m = F^k(n) = m'+1
  -- prefix L(m) = prefix (n-1) ++ block', where block' = tau^k([x[m']])
  have hprefix : hofPrefix k (imageLength k k ((hofstadterF k)^[k] n)) =
      hofPrefix k (n - 1) ++ (hofTauList k)^[k] [hofWord k ((hofstadterF k)^[k] (n - 1))] := by
    have h1 : (hofstadterF k)^[k] n = (hofstadterF k)^[k] (n - 1) + 1 := E
    rw [h1]
    have h2 := prefix_image_succ k k ((hofstadterF k)^[k] (n - 1))
    rw [HL'] at h2
    exact h2
  have ha_le := (letter_bounds (by omega : 1 ≤ k) ((hofstadterF k)^[k] (n - 1))).2
  have ha_ge := (letter_bounds (by omega : 1 ≤ k) ((hofstadterF k)^[k] (n - 1))).1
  have hblock := iterate_letter ha_le (le_refl k)
    (by omega : k ≤ hofWord k ((hofstadterF k)^[k] (n - 1)) + k)
  have harith : hofWord k ((hofstadterF k)^[k] (n - 1)) + k - k =
      hofWord k ((hofstadterF k)^[k] (n - 1)) := by omega
  rw [harith] at hblock
  rw [hblock] at hprefix
  have hL : imageLength k k ((hofstadterF k)^[k] n) =
      (n - 1) + (hofWord k ((hofstadterF k)^[k] (n - 1)) + 1) := by
    rw [E, image_succ, HL', hblock]
    simp
  have hlt1 : n - 1 < imageLength k k ((hofstadterF k)^[k] n) := by omega
  have hlt2 : n < imageLength k k ((hofstadterF k)^[k] n) := by omega
  have hle1 : n - 1 ≤ n - 1 := Nat.le_refl _
  have hle2 : n - 1 ≤ n := by omega
  have hx1 : hofWord k (n - 1) = k := by
    have he1 := congrArg (fun w : List ℕ => w[n - 1]?) hprefix
    simpa [hofPrefix_eq_map, List.getElem?_append_right, hlt1, hle1] using he1
  have hx2 : hofWord k n = 1 := by
    have hq := block_getElem_q_aux2 k (hofWord k ((hofstadterF k)^[k] (n - 1))) 1
      (by omega) (by omega)
    have he2 := congrArg (fun w : List ℕ => w[n]?) hprefix
    have hn_eq : n - (n - 1) = 1 := by omega
    simpa [hofPrefix_eq_map, List.getElem?_append_right, hlt2, hle2, hq, hn_eq] using he2
  exact ⟨hx1, hx2⟩

private theorem steiner_step_final_aux {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (E : (hofstadterF k)^[k] n = (hofstadterF k)^[k] (n - 1) + 1)
    (IHn1_1 : LBound_aux k 1 (n - 1) (hofstadterF k (n - 1)))
    (IHn_1 : LBound_aux k 1 n (hofstadterF k n))
    (IHn1_k : LBound_aux k k (n - 1) ((hofstadterF k)^[k] (n - 1)))
    (IHn_k : LBound_aux k k n ((hofstadterF k)^[k] n)) :
    LBound_aux k 1 (n + 1) (hofstadterF k (n + 1)) := by
  have hFS : hofstadterF k (n + 1) = hofstadterF k n := by
    have hFn : hofstadterF k n = n - (hofstadterF k)^[k] (n - 1) := by
      have hs := hofstadterF_succ_eq k (n - 1)
      rw [show (n - 1) + 1 = n by omega] at hs
      exact hs
    rw [hofstadterF_succ_eq k n, hFn, E]
    have hle := iterate_le_aux k k (n - 1)
    omega
  have hE' : hofstadterF k n = hofstadterF k (n - 1) + 1 :=
    steiner_step_E_aux hk hn E
  have hHL : imageLength k 1 (hofstadterF k (n - 1)) = n - 1 := by
    simp only [LBound_aux] at IHn1_1 IHn_1
    have hsub : hofstadterF k n - 1 = hofstadterF k (n - 1) := by omega
    rw [hsub] at IHn_1
    omega
  have hHL' : imageLength k k ((hofstadterF k)^[k] (n - 1)) = n - 1 := by
    simp only [LBound_aux] at IHn1_k IHn_k
    have hsub : (hofstadterF k)^[k] n - 1 = (hofstadterF k)^[k] (n - 1) := by omega
    rw [hsub] at IHn_k
    omega
  obtain ⟨hH1, hH2⟩ := steiner_step_H_aux hk hn E hHL'
  -- Now show x[F(n-1)] = k by contradiction using 1-blocks and H
  have hxFk : hofWord k (hofstadterF k (n - 1)) = k := by
    by_contra hne
    have hb1 := letter_bounds (by omega : 1 ≤ k) (hofstadterF k (n - 1))
    have hb2 := letter_bounds (by omega : 1 ≤ k) (hofstadterF k n)
    have hblock1 : (hofTauList k)^[1] [hofWord k (hofstadterF k (n - 1))] =
        [hofWord k (hofstadterF k (n - 1)) + 1] := by
      rw [block_one_eq]
      simp [hofTau, hne]
    have hEL : (hofTauList k)^[1] (hofPrefix k (hofstadterF k (n - 1))) =
        hofPrefix k (n - 1) := by
      rw [iterate_prefix, hHL]
    have hprefix2 : hofPrefix k (hofstadterF k (n - 1) + 2) =
        hofPrefix k (hofstadterF k (n - 1)) ++
          [hofWord k (hofstadterF k (n - 1)), hofWord k (hofstadterF k n)] := by
      have hs1 := prefix_succ k (hofstadterF k (n - 1))
      have hs2 := prefix_succ k (hofstadterF k (n - 1) + 1)
      have heq : hofstadterF k (n - 1) + 1 + 1 = hofstadterF k (n - 1) + 2 := by omega
      have heq2 : hofstadterF k (n - 1) + 1 = hofstadterF k n := by omega
      rw [heq] at hs2
      rw [hs2, hs1, heq2]
      simp [List.append_assoc]
    have htau2 : (hofTauList k)^[1] (hofPrefix k (hofstadterF k (n - 1) + 2)) =
        hofPrefix k (n - 1) ++ (hofTauList k)^[1] [hofWord k (hofstadterF k (n - 1))] ++
          (hofTauList k)^[1] [hofWord k (hofstadterF k n)] := by
      rw [hprefix2, iterate_append]
      have hab : [hofWord k (hofstadterF k (n - 1)), hofWord k (hofstadterF k n)] =
          [hofWord k (hofstadterF k (n - 1))] ++ [hofWord k (hofstadterF k n)] := rfl
      rw [hab, iterate_append, hEL]
      simp [List.append_assoc]
    have hLp : hofPrefix k (imageLength k 1 (hofstadterF k (n - 1) + 2)) =
        hofPrefix k (n - 1) ++ (hofTauList k)^[1] [hofWord k (hofstadterF k (n - 1))] ++
          (hofTauList k)^[1] [hofWord k (hofstadterF k n)] := by
      rw [← iterate_prefix]
      exact htau2
    rw [hblock1] at hLp
    have hL1 : imageLength k 1 (hofstadterF k (n - 1) + 1) = n := by
      have hs := image_succ k 1 (hofstadterF k (n - 1))
      rw [hHL, hblock1] at hs
      simp only [List.length_cons, List.length_nil] at hs
      omega
    have hL2ge : n + 1 ≤ imageLength k 1 (hofstadterF k (n - 1) + 2) := by
      have hs := image_succ k 1 (hofstadterF k (n - 1) + 1)
      rw [hL1] at hs
      have hadd : hofstadterF k (n - 1) + 1 + 1 = hofstadterF k (n - 1) + 2 := by omega
      rw [hadd] at hs
      have hlen : 1 ≤ ((hofTauList k)^[1] [hofWord k (hofstadterF k (n - 1) + 1)]).length := by
        rw [block_one_eq]
        exact one_le_length_hofTau k _
      omega
    have hx_nm1 : hofWord k (n - 1) = hofWord k (hofstadterF k (n - 1)) + 1 := by
      have he1 := congrArg (fun w : List ℕ => w[n - 1]?) hLp
      have hlt1 : n - 1 < imageLength k 1 (hofstadterF k (n - 1) + 2) := by omega
      have hle1 : n - 1 ≤ n - 1 := Nat.le_refl _
      simpa [hofPrefix_eq_map, List.getElem?_append_right, hlt1, hle1] using he1
    have hxb : hofWord k (hofstadterF k (n - 1)) + 1 = k := by omega
    have hlt2 : n < imageLength k 1 (hofstadterF k (n - 1) + 2) := by omega
    have hle2 : n - 1 ≤ n := by omega
    have hn_sub : n - (n - 1) = 1 := by omega
    by_cases hb : hofWord k (hofstadterF k n) = k
    · have hblock2 : (hofTauList k)^[1] [hofWord k (hofstadterF k n)] = [k, 1] := by
        rw [block_one_eq]
        simp [hofTau, hb]
      rw [hblock2] at hLp
      have he2 := congrArg (fun w : List ℕ => w[n]?) hLp
      have hx_nk : hofWord k n = k := by
        simpa [hofPrefix_eq_map, List.getElem?_append_right, hlt2, hle2, hn_sub] using he2
      omega
    · have hblock2 : (hofTauList k)^[1] [hofWord k (hofstadterF k n)] =
          [hofWord k (hofstadterF k n) + 1] := by
        rw [block_one_eq]
        simp [hofTau, hb]
      rw [hblock2] at hLp
      have he2 := congrArg (fun w : List ℕ => w[n]?) hLp
      have hx_nb : hofWord k n = hofWord k (hofstadterF k n) + 1 := by
        simpa [hofPrefix_eq_map, List.getElem?_append_right, hlt2, hle2, hn_sub] using he2
      omega
  -- With x[F(n-1)] = k, block1 length 2, so L(F(n)) = (n-1)+2 = n+1
  have hL2 : n + 1 ≤ imageLength k 1 (hofstadterF k (n + 1)) := by
    rw [hFS, hE']
    have hs := image_succ k 1 (hofstadterF k (n - 1))
    rw [hHL] at hs
    -- hs : L(F(n-1)+1) = (n-1) + |tau([x[F(n-1)]])|
    -- With hxFk (x[F(n-1)]=k), |tau([k])| = 2 (via block_one_eq + hofTau)
    have hlen : ((hofTauList k)^[1] [hofWord k (hofstadterF k (n - 1))]).length = 2 := by
      rw [block_one_eq, hxFk]
      simp [hofTau]
    omega
  simp only [LBound_aux] at IHn_1 ⊢
  rw [hFS] at hL2 ⊢
  constructor
  · omega
  · exact hL2

private theorem steiner_corestep_aux {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (IHn1 : ∀ j, SteinerThm_aux k j (n - 1))
    (IHn : ∀ j, SteinerThm_aux k j n) :
    SteinerThm_aux k 1 (n + 1) := by
  intro _
  have hstep := iterate_step_aux k k (n - 1)
  have hn_eq : (n - 1) + 1 = n := by omega
  rw [hn_eq] at hstep
  rcases hstep with E | E
  · have hdisj := steiner_disj_aux (show 1 ≤ n by omega)
      (IHn 1 (by omega))
    rcases hdisj with EQ | EQ2
    · exact steiner_corestep_flat_eq hn E EQ
    · exfalso
      exact steiner_exfalso_aux hk hn E EQ2 (IHn k (by omega)) (IHn1 k (by omega))
  · exact steiner_step_final_aux hk hn E (IHn1 1 (by omega)) (IHn 1 (by omega))
      (IHn1 k (by omega)) (IHn k (by omega))

private theorem length_le_image_general_aux (k j : ℕ) (w : List ℕ) :
    w.length ≤ ((hofTauList k)^[j] w).length := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (length_le_length_hofTauList k _)

private theorem le_image_general_aux (k j n : ℕ) : n ≤ imageLength k j n := by
  have h := length_le_image_general_aux k j (hofPrefix k n)
  rw [prefix_length] at h
  exact h

private theorem image_zero_right_aux (k n : ℕ) : imageLength k 0 n = n := by
  have h : (hofTauList k)^[0] (hofPrefix k n) = hofPrefix k n := rfl
  unfold imageLength
  rw [h, prefix_length]

private theorem iterate_succ_two_aux (k j : ℕ) : (hofstadterF k)^[j + 1] 2 = 1 := by
  rw [Function.iterate_succ_apply, hofstadterF_two_aux]
  exact iterate_one_eq_aux k j

private theorem steiner_all_aux {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    ∀ j, SteinerThm_aux k j n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hn0
    by_cases hn2 : n ≤ 2
    · have hn12 : n = 1 ∨ n = 2 := by omega
      rcases hn12 with rfl | rfl
      · rw [iterate_one_eq_aux]
        simp only [LBound_aux]
        rw [show (1 : ℕ) - 1 = 0 from rfl, image_zero]
        constructor
        · omega
        · exact le_image_general_aux k j 1
      · cases j with
        | zero =>
          simp only [LBound_aux]
          have hF0 : (hofstadterF k)^[0] 2 = 2 := rfl
          rw [hF0]
          rw [show (2 : ℕ) - 1 = 1 from rfl, image_zero_right_aux, image_zero_right_aux]
          constructor <;> omega
        | succ j =>
          have hF : (hofstadterF k)^[j + 1] 2 = 1 := iterate_succ_two_aux k j
          simp only [LBound_aux]
          rw [hF]
          rw [show (1 : ℕ) - 1 = 0 from rfl, image_zero]
          constructor
          · omega
          · have h1 : imageLength k 1 1 = 2 := image_one (by omega : 1 ≤ k)
            have hadd := image_add_aux k j 1 1
            rw [h1] at hadd
            rw [hadd]
            exact le_image_general_aux k j 2
    · have hn2' : 2 < n := by omega
      have hn_ge : 2 ≤ n - 1 := by omega
      have hn_eq : (n - 1) + 1 = n := by omega
      have hJ1 : SteinerThm_aux k 1 n := by
        rw [← hn_eq]
        exact steiner_corestep_aux hk hn_ge (ih _ (by omega)) (ih _ (by omega))
      cases j with
      | zero =>
        simp only [LBound_aux]
        have hF0 : (hofstadterF k)^[0] n = n := rfl
        rw [hF0, image_zero_right_aux, image_zero_right_aux]
        constructor <;> omega
      | succ j =>
        have hFn_lt : hofstadterF k n < n := hofstadterF_lt_aux k n (by omega)
        have hFn_pos : 0 < hofstadterF k n := hofstadterF_nonzero_aux k n (by omega)
        have hIH := ih _ hFn_lt j hFn_pos
        simp only [LBound_aux] at hIH
        have hFsucc : (hofstadterF k)^[j + 1] n = (hofstadterF k)^[j] (hofstadterF k n) := by
          rw [Function.iterate_succ_apply]
        have hmono := (image_strictMono (show 1 ≤ k by omega) (show 1 ≤ k by omega)).monotone
        have hle1 : imageLength k j ((hofstadterF k)^[j + 1] n - 1) ≤
            hofstadterF k n - 1 := by
          rw [hFsucc]
          omega
        have hle2 : hofstadterF k n ≤ imageLength k j ((hofstadterF k)^[j + 1] n) := by
          rw [hFsucc]
          exact hIH.2
        have hadd1 : imageLength k (j + 1) ((hofstadterF k)^[j + 1] n - 1) =
            imageLength k 1 (imageLength k j ((hofstadterF k)^[j + 1] n - 1)) := by
          have h := image_add_aux k 1 j ((hofstadterF k)^[j + 1] n - 1)
          rwa [show (1 : ℕ) + j = j + 1 by omega] at h
        have hadd2 : imageLength k (j + 1) ((hofstadterF k)^[j + 1] n) =
            imageLength k 1 (imageLength k j ((hofstadterF k)^[j + 1] n)) := by
          have h := image_add_aux k 1 j ((hofstadterF k)^[j + 1] n)
          rwa [show (1 : ℕ) + j = j + 1 by omega] at h
        have hm1 := hmono hle1
        have hm2 := hmono hle2
        rw [← hadd1] at hm1
        rw [← hadd2] at hm2
        have hJ1b := hJ1 hn0
        simp only [LBound_aux] at hJ1b
        simp only [LBound_aux]
        exact ⟨lt_of_le_of_lt hm1 hJ1b.1, hJ1b.2.trans hm2⟩

private theorem lbound_unique_aux {k j n a b : ℕ} (hk : 1 ≤ k) (hj : j ≤ k)
    (ha : LBound_aux k j n a) (hb : LBound_aux k j n b) : a = b := by
  simp only [LBound_aux] at ha hb
  have hmono := (image_strictMono hk hj).monotone
  by_contra hne
  have hlt : a < b ∨ b < a := by omega
  rcases hlt with h | h
  · have hab : a ≤ b - 1 := by omega
    have hle := hmono hab
    omega
  · have hab : b ≤ a - 1 := by omega
    have hle := hmono hab
    omega

private theorem hofcount_eq_steiner_aux {k n : ℕ} (hk : 2 ≤ k) (hn0 : 0 < n) :
    hofCount k (· = k) n = (hofstadterF k)^[k - 1] n := by
  have hk1 : 1 ≤ k := by omega
  have hj : k - 1 ≤ k := by omega
  have hC2 : n ≤ imageLength k (k - 1) (hofCount k (· = k) n) :=
    count_covers (· = k) (fun c => (top_boundary hk1 c).2) n
  have hC1 : imageLength k (k - 1) (hofCount k (· = k) n - 1) < n := by
    by_cases hC0 : hofCount k (· = k) n = 0
    · rw [hC0]
      have h0 : (0 : ℕ) - 1 = 0 := rfl
      rw [h0, image_zero]
      exact hn0
    · by_contra! hlt
      have hmono := count_mono k (· = k) hlt
      rw [(top_boundary hk1 (hofCount k (· = k) n - 1)).1] at hmono
      omega
  have hCb : LBound_aux k (k - 1) n (hofCount k (· = k) n) := ⟨hC1, hC2⟩
  have hFb : LBound_aux k (k - 1) n ((hofstadterF k)^[k - 1] n) :=
    steiner_all_aux hk n (k - 1) hn0
  exact lbound_unique_aux hk1 hj hCb hFb

private theorem hofCount_eq_iterate (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    hofCount k (· = k) n = (hofstadterF k)^[k - 1] n := by
  cases n with
  | zero =>
    simp [hofCount, hofPrefix_eq_map, iterate_zero_eq_aux]
  | succ n =>
    by_cases hk1 : k = 1
    · subst hk1
      rw [hofCount_one_eq]
      rfl
    · have hk2 : 2 ≤ k := by omega
      exact hofcount_eq_steiner_aux hk2 (by omega : 0 < n + 1)


@[expose] public section

/-- **The image length $L_k$ as a letter count.** Let $k \ge 1$. Let $F_k$ be the generalized
Hofstadter function and $F_k^{k-1}$ its $(k-1)$-fold iterate, let $x_k[0]\,x_k[1] \cdots$ be the
fixed point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, let $L_k(n)$ be the length of the word
$\tau_k(x_k[0] \cdots x_k[n-1])$, and let $C_k^{(=k)}(n)$ be the number of indices $0 \le i < n$
with $x_k[i] = k$. Then for every natural number $n$, $L_k(n) = n + C_k^{(=k)}(n)$ and
$L_k(n) = n + F_k^{k-1}(n)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 4.2 (`jis-2026-26.3.3-prop-9`). -/
public theorem hofL_eq_add_hofCount {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    hofL k n = n + hofCount k (· = k) n ∧ hofL k n = n + (hofstadterF k)^[k - 1] n := by
  have h : hofL k n = n + hofCount k (· = k) n := image_eq_add_count k n
  exact ⟨h, by rw [h, hofCount_eq_iterate k hk n]⟩

end

end MetaMathlibExt
