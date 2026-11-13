/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section


/-- In Dijkstra's token ring on `n + 1` machines arranged on a
ring (indices in `ZMod (n + 1)`), machine `0` is privileged
when its state equals its predecessor's; every other machine
is privileged when its state differs from its predecessor's. -/
def privileged {n K : ℕ} (x : ZMod (n + 1) → ZMod K)
    (i : ZMod (n + 1)) : Prop :=
  if i = 0 then x 0 = x (-1) else x i ≠ x (i - 1)

/-- The value a privileged machine moves to: machine `0`
increments, every other machine copies its predecessor. -/
def moveVal {n K : ℕ} (x : ZMod (n + 1) → ZMod K)
    (i : ZMod (n + 1)) : ZMod K :=
  if i = 0 then x 0 + 1 else x (i - 1)

/-- One central-daemon step: a privileged machine moves. -/
def Step {n K : ℕ} (x y : ZMod (n + 1) → ZMod K) : Prop :=
  ∃ i, privileged x i ∧ y = Function.update x i (moveVal x i)

/-- A legitimate configuration has exactly one privileged
machine. -/
def Legit {n K : ℕ} (x : ZMod (n + 1) → ZMod K) : Prop :=
  ∃! i, privileged x i

private lemma priv_zero {n K : ℕ} {x : ZMod (n + 1) → ZMod K} :
    privileged x 0 ↔ x 0 = x (-1) := by
  unfold privileged
  simp

private lemma priv_ne {n K : ℕ} {x : ZMod (n + 1) → ZMod K} {i : ZMod (n + 1)}
    (hi : i ≠ 0) : privileged x i ↔ x i ≠ x (i - 1) := by
  unfold privileged
  simp [hi]

private lemma moveVal_zero {n K : ℕ} {x : ZMod (n + 1) → ZMod K} :
    moveVal x 0 = x 0 + 1 := by
  unfold moveVal
  simp

private lemma moveVal_ne {n K : ℕ} {x : ZMod (n + 1) → ZMod K} {i : ZMod (n + 1)}
    (hi : i ≠ 0) : moveVal x i = x (i - 1) := by
  unfold moveVal
  simp [hi]

private lemma one_ne_zero_of {n : ℕ} (hn : 1 ≤ n) : (1 : ZMod (n + 1)) ≠ 0 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod (n + 1)) = 0 := by
    rw [Nat.cast_one]
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have hle : n + 1 ≤ 1 := Nat.le_of_dvd zero_lt_one h1
  omega

private lemma neg_one_ne_zero_of {n : ℕ} (hn : 1 ≤ n) :
    (-1 : ZMod (n + 1)) ≠ 0 := by
  intro h
  have h1 : (1 : ZMod (n + 1)) = 0 := by
    have h2 := congrArg Neg.neg h
    simpa using h2
  exact one_ne_zero_of hn h1

private lemma chain_wrap {n K : ℕ} {x : ZMod (n + 1) → ZMod K} {i : ZMod (n + 1)}
    (heq : ∀ j, j ≠ 0 → j ≠ i → x j = x (j - 1)) (hwrap : i + 1 = 0) :
    ∀ j, j ≠ i → x j = x 0 := by
  have key : ∀ (k : ℕ) (j : ZMod (n + 1)),
      j = ((k : ℕ) : ZMod (n + 1)) → j ≠ i → x j = x 0 := by
    intro k
    induction k with
    | zero =>
      intro j hj _
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      rfl
    | succ k ih =>
      intro j hj hji
      by_cases hj0 : j = 0
      · subst hj0
        rfl
      · have hsub : j - 1 = ((k : ℕ) : ZMod (n + 1)) := by
          simp only [hj, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        have hjm : ((k : ℕ) : ZMod (n + 1)) ≠ i := by
          rw [← hsub]
          intro hcon
          apply hj0
          have h2 : (j - 1) + 1 = i + 1 := by rw [hcon]
          rw [sub_add_cancel] at h2
          rw [h2, hwrap]
        rw [heq j hj0 hji, hsub]
        exact ih _ rfl hjm
  intro j hji
  exact key _ _ (ZMod.natCast_zmod_val j).symm hji

/-- Non-deadlock: every configuration has a privileged
machine. -/
theorem exists_privileged {n K : ℕ} (x : ZMod (n + 1) → ZMod K) :
    ∃ i, privileged x i := by
  by_contra hnone
  have hnone : ∀ i, ¬ privileged x i := fun i hi => hnone ⟨i, hi⟩
  have h0' : x 0 ≠ x (-1) := by
    have h := hnone 0
    rwa [priv_zero] at h
  have heq : ∀ i : ZMod (n + 1), i ≠ 0 → x i = x (i - 1) := by
    intro i hi
    have h := hnone i
    rw [priv_ne hi] at h
    exact not_ne_iff.mp h
  have key : ∀ (k : ℕ) (i : ZMod (n + 1)),
      i = ((k : ℕ) : ZMod (n + 1)) → x i = x 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      rfl
    | succ k ih =>
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        rfl
      · have hsub : i - 1 = ((k : ℕ) : ZMod (n + 1)) := by
          simp only [hi, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        rw [heq i hi0, hsub]
        exact ih _ rfl
  have hcon : x (-1) = x 0 := key _ _ (ZMod.natCast_zmod_val (-1)).symm
  exact h0' hcon.symm

/-- Closure: legitimate configurations are closed under
steps. (Convergence to legitimacy, the other half of roadmap
package DPA-15, remains open.) -/
theorem legit_closed {n K : ℕ} {x y : ZMod (n + 1) → ZMod K}
    (hx : Legit x) (hstep : Step x y) : Legit y := by
  obtain ⟨i, hpriv_i, rfl⟩ := hstep
  obtain ⟨m, hm_priv, hm_uniq⟩ := hx
  have hi_eq : i = m := hm_uniq i hpriv_i
  subst hi_eq
  have hunpriv : ∀ j, j ≠ i → ¬ privileged x j := fun j hj hp => hj (hm_uniq j hp)
  by_cases hn : n = 0
  · subst hn
    have hsub : ∀ a b : ZMod (0 + 1), a = b := by
      intro a b
      have ha : a.val = 0 := by
        have hlt := ZMod.val_lt a
        omega
      have hb : b.val = 0 := by
        have hlt := ZMod.val_lt b
        omega
      have h : a.val = b.val := by omega
      calc a = ((a.val : ℕ) : ZMod (0 + 1)) := (ZMod.natCast_zmod_val a).symm
        _ = ((b.val : ℕ) : ZMod (0 + 1)) := by rw [h]
        _ = b := ZMod.natCast_zmod_val b
    refine ⟨0, priv_zero.mpr ?_, ?_⟩
    · exact congrArg _ (hsub 0 (-1))
    · intro j _
      exact hsub j 0
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have h1ne : (1 : ZMod (n + 1)) ≠ 0 := one_ne_zero_of hn1
    have hneg1ne : (-1 : ZMod (n + 1)) ≠ 0 := neg_one_ne_zero_of hn1
    by_cases hi0 : i = 0
    · subst hi0
      have hx0 : x 0 = x (-1) := priv_zero.mp hm_priv
      have hx1 : x 1 = x 0 := by
        have h := hunpriv 1 h1ne
        rw [priv_ne h1ne] at h
        have h2 := not_ne_iff.mp h
        rwa [sub_self] at h2
      have hmv : moveVal x 0 = x 0 + 1 := moveVal_zero
      have hy0 : Function.update x 0 (moveVal x 0) 0 = x 0 + 1 := by
        rw [hmv]
        exact Function.update_self 0 _ x
      have hy_ne : ∀ j, j ≠ 0 → Function.update x 0 (moveVal x 0) j = x j :=
        fun j hj => Function.update_of_ne hj _ _
      have hstatus0 : privileged (Function.update x 0 (moveVal x 0)) 0 ↔
          (1 : ZMod K) = 0 := by
        rw [priv_zero, hy0, hy_ne (-1) hneg1ne, ← hx0]
        constructor
        · intro h
          have h2 : x 0 + 1 = x 0 + 0 := by
            rw [add_zero]
            exact h
          exact add_left_cancel_iff.mp h2
        · intro h
          rw [h, add_zero]
      have hstatus1 : privileged (Function.update x 0 (moveVal x 0)) 1 ↔
          (1 : ZMod K) ≠ 0 := by
        rw [priv_ne h1ne, hy_ne 1 h1ne, sub_self, hy0, hx1]
        constructor
        · intro h hcon
          apply h
          rw [hcon, add_zero]
        · intro h hcon
          apply h
          have h2 : x 0 + 1 = x 0 + 0 := by
            rw [add_zero]
            exact hcon.symm
          exact add_left_cancel_iff.mp h2
      have hother : ∀ j, j ≠ 0 → j ≠ 1 →
          ¬ privileged (Function.update x 0 (moveVal x 0)) j := by
        intro j hj0 hj1 hpj
        have hyj := hy_ne j hj0
        have hyjm : Function.update x 0 (moveVal x 0) (j - 1) = x (j - 1) := by
          apply hy_ne
          intro hcon
          apply hj1
          have h2 : (j - 1) + 1 = 0 + 1 := by rw [hcon]
          rw [sub_add_cancel, zero_add] at h2
          exact h2
        rw [priv_ne hj0, hyj, hyjm] at hpj
        exact hj0 (hm_uniq j ((priv_ne hj0).mpr hpj))
      by_cases hK : (1 : ZMod K) = 0
      · refine ⟨0, hstatus0.mpr hK, ?_⟩
        intro j hpj
        by_cases hj0 : j = 0
        · exact hj0
        · by_cases hj1 : j = 1
          · subst hj1
            exact absurd hK (hstatus1.mp hpj)
          · exact absurd hpj (hother j hj0 hj1)
      · refine ⟨1, hstatus1.mpr hK, ?_⟩
        intro j hpj
        by_cases hj1 : j = 1
        · exact hj1
        · by_cases hj0 : j = 0
          · subst hj0
            exact absurd (hstatus0.mp hpj) hK
          · exact absurd hpj (hother j hj0 hj1)
    · have hmv : moveVal x i = x (i - 1) := moveVal_ne hi0
      have hpx : x i ≠ x (i - 1) := (priv_ne hi0).mp hpriv_i
      have hy_i : Function.update x i (moveVal x i) i = x (i - 1) := by
        rw [hmv]
        exact Function.update_self i _ x
      have hy_ne : ∀ j, j ≠ i → Function.update x i (moveVal x i) j = x j :=
        fun j hj => Function.update_of_ne hj _ _
      have hsucc_ne : i + 1 ≠ i := by
        intro hcon
        apply h1ne
        have h2 : i + 1 = i + 0 := by
          rw [add_zero]
          exact hcon
        exact add_left_cancel_iff.mp h2
      have hpre_ne : i - 1 ≠ i := by
        intro hcon
        have h4 : (i - 1) + 1 = i + 1 := by rw [hcon]
        rw [sub_add_cancel] at h4
        exact hsucc_ne h4.symm
      have hi_unpriv : ¬ privileged (Function.update x i (moveVal x i)) i := by
        rw [priv_ne hi0, hy_i, hy_ne (i - 1) hpre_ne]
        exact not_ne_iff.mpr rfl
      have heq : ∀ j, j ≠ 0 → j ≠ i → x j = x (j - 1) := by
        intro j hj0 hji
        have h := hunpriv j hji
        rw [priv_ne hj0] at h
        exact not_ne_iff.mp h
      have hsucc_priv : privileged (Function.update x i (moveVal x i)) (i + 1) := by
        by_cases hwrap : i + 1 = 0
        · rw [hwrap, priv_zero]
          have hy0' : Function.update x i (moveVal x i) 0 = x 0 :=
            hy_ne 0 (Ne.symm hi0)
          have hneg : (-1 : ZMod (n + 1)) = i := by
            have h : i = -(1 : ZMod (n + 1)) := eq_neg_of_add_eq_zero_left hwrap
            rw [h]
          rw [hy0', hneg, hy_i]
          exact (chain_wrap heq hwrap (i - 1) hpre_ne).symm
        · rw [priv_ne hwrap]
          have hy_succ : Function.update x i (moveVal x i) (i + 1) = x (i + 1) :=
            hy_ne _ hsucc_ne
          have hcast : i + 1 - 1 = i := add_sub_cancel_right _ _
          rw [hy_succ, hcast, hy_i]
          have hx_succ : x (i + 1) = x i := by
            have h := hunpriv (i + 1) hsucc_ne
            rw [priv_ne hwrap] at h
            have h2 := not_ne_iff.mp h
            rwa [hcast] at h2
          rw [hx_succ]
          exact hpx
      have hother : ∀ j, j ≠ i → j ≠ i + 1 →
          ¬ privileged (Function.update x i (moveVal x i)) j := by
        intro j hji hjs hpj
        have hyj := hy_ne j hji
        have hyjm : Function.update x i (moveVal x i) (j - 1) = x (j - 1) := by
          apply hy_ne
          intro hcon
          apply hjs
          have h2 : (j - 1) + 1 = i + 1 := by rw [hcon]
          rw [sub_add_cancel] at h2
          exact h2
        by_cases hj0 : j = 0
        · subst hj0
          have hne : (-1 : ZMod (n + 1)) ≠ i := by
            intro hcon
            apply hjs
            rw [← hcon, neg_add_cancel]
          have hy0' := hy_ne 0 hji
          have hyn1 := hy_ne (-1) hne
          rw [priv_zero, hy0', hyn1] at hpj
          exact hji (hm_uniq 0 (priv_zero.mpr hpj))
        · rw [priv_ne hj0, hyj, hyjm] at hpj
          exact hji (hm_uniq j ((priv_ne hj0).mpr hpj))
      refine ⟨i + 1, hsucc_priv, ?_⟩
      intro j hpj
      by_cases hjs : j = i + 1
      · exact hjs
      · by_cases hji : j = i
        · subst hji
          exact absurd hpj hi_unpriv
        · exact absurd hpj (hother j hji hjs)
