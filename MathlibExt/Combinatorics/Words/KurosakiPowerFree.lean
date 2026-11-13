/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

namespace Kurosaki

private def kurS01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def kurS12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private def kurTau : ℕ → Equiv.Perm (Fin 3)
  | 0 => kurS01
  | 1 => 1
  | _ + 1 + 1 => kurS12

private def kurGam : ℕ → Equiv.Perm (Fin 3)
  | 0 => 1
  | n + 1 => kurS01 * kurGam ((n + 1) / 3) * kurTau ((n + 1) % 3)
termination_by n => n
decreasing_by
  simp_wf
  omega

private def kurSigFn : Fin 3 → Fin 3 := fun a => if a.val = 0 then 1 else if a.val = 1 then 0 else 2
private def kurRhoFn : Fin 3 → Fin 3 := fun a => if a.val = 1 then 2 else if a.val = 2 then 1 else 0

private def kurW : ℕ → List (Fin 3) := fun n => Nat.rec (motive := fun _ => List (Fin 3))
    [(1 : Fin 3)]
  (fun _ ih => (List.map kurSigFn ih ++ ih) ++ List.map kurRhoFn ih) n

private theorem kurGam_zero : kurGam 0 = 1 := by
  have h := kurGam.induct_unfolding
    (motive := fun a g => g = match a with
      | 0 => (1 : Equiv.Perm (Fin 3))
      | n + 1 => kurS01 * kurGam ((n + 1) / 3) * kurTau ((n + 1) % 3))
    (rfl) (fun _ _ => rfl) (0)
  simpa using h

private theorem kurGam_succ (n : ℕ) :
    kurGam (n + 1) = kurS01 * kurGam ((n + 1) / 3) * kurTau ((n + 1) % 3) := by
  have h := kurGam.induct_unfolding
    (motive := fun a g => g = match a with
      | 0 => (1 : Equiv.Perm (Fin 3))
      | n + 1 => kurS01 * kurGam ((n + 1) / 3) * kurTau ((n + 1) % 3))
    (rfl) (fun _ _ => rfl) (n + 1)
  simpa using h

private theorem kurTau_zero : kurTau 0 = kurS01 := rfl
private theorem kurTau_one : kurTau 1 = 1 := rfl
private theorem kurTau_two : kurTau 2 = kurS12 := rfl

private theorem kurS01_sq : kurS01 * kurS01 = 1 := Equiv.swap_mul_self 0 1
private theorem kurS01_sq2 : kurS01 ^ 2 = 1 := by rw [pow_two]; exact kurS01_sq
private theorem kurS01_pow_even (t : ℕ) : kurS01 ^ (2 * t) = 1 := by
  rw [pow_mul, kurS01_sq2, one_pow]
private theorem kurS01_sq_mul (n : ℕ) : kurS01 ^ (n + 1) * kurS01 ^ n = kurS01 := by
  rw [← pow_add, show n + 1 + n = 2 * n + 1 from by omega, pow_add,
    kurS01_pow_even, pow_one, one_mul]

private theorem kurGam_three_mul_add (k d : ℕ) (hd : d < 3) :
    kurGam (3 * k + d) = kurS01 * kurGam k * kurTau d := by
  by_cases hkd : 3 * k + d = 0
  · have hk : k = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hk; subst hd0
    simp [kurGam_zero, kurTau_zero, kurS01_sq]
  · obtain ⟨n, hn⟩ : ∃ n, 3 * k + d = n + 1 := ⟨3 * k + d - 1, by omega⟩
    rw [hn, kurGam_succ]
    have hdiv : (n + 1) / 3 = k := by omega
    have hmod : (n + 1) % 3 = d := by omega
    rw [hdiv, hmod]

private theorem kurGam_one : kurGam 1 = kurS01 := by
  have h := kurGam_three_mul_add 0 1 (by omega)
  simpa [kurGam_zero, kurTau_one] using h

private theorem kurGam_two : kurGam 2 = kurS01 * kurS12 := by
  have h := kurGam_three_mul_add 0 2 (by omega)
  simpa [kurGam_zero, kurTau_two] using h

private theorem kurGam_top_digit (n j k : ℕ) (hk : k < 3 ^ n) :
    kurGam (j * 3 ^ n + k) = kurS01 ^ n * kurGam j * kurS01 ^ n * kurGam k := by
  induction n generalizing j k with
  | zero =>
    simp only [pow_zero, Order.lt_one_iff]at hk; subst hk
    simp [kurGam_zero]
  | succ n ih =>
    have hmod3 : k % 3 < 3 := Nat.mod_lt _ (by omega)
    have h3 : k < 3 ^ n * 3 := by rwa [pow_succ] at hk
    have hdiv : k / 3 < 3 ^ n := by omega
    have hksplit : k = 3 * (k / 3) + k % 3 := (Nat.div_add_mod k 3).symm
    have hpow : j * 3 ^ (n + 1) = 3 * (j * 3 ^ n) := by rw [pow_succ]; ring
    have key : j * 3 ^ (n + 1) + k = 3 * (j * 3 ^ n + k / 3) + k % 3 := by
      rw [hpow]; omega
    have e1 : kurGam k = kurS01 * kurGam (k / 3) * kurTau (k % 3) := by
      conv_lhs => rw [hksplit]
      exact kurGam_three_mul_add _ _ hmod3
    have hkk2 : kurGam (k / 3) * kurTau (k % 3) = kurS01 * kurGam k := by
      have h2 := congrArg (kurS01 * ·) e1
      simp only [← mul_assoc, kurS01_sq, one_mul] at h2
      exact h2.symm
    have push : ∀ X : Equiv.Perm (Fin 3),
        kurS01 * (kurS01 ^ n * X) = kurS01 ^ (n + 1) * X := by
      intro X; rw [← mul_assoc, ← pow_succ']
    have pull : ∀ X : Equiv.Perm (Fin 3),
        kurS01 ^ n * (kurS01 * X) = kurS01 ^ (n + 1) * X := by
      intro X; rw [← mul_assoc, ← pow_succ]
    have ih1 := ih j (k / 3) hdiv
    rw [key, kurGam_three_mul_add _ _ hmod3, ih1]
    simp only [mul_assoc]
    rw [hkk2, push, pull]

private theorem kurSigFn_eq (a : Fin 3) : kurSigFn a = kurS01 a := by
  fin_cases a <;> decide

private theorem kurRhoFn_eq (a : Fin 3) : kurRhoFn a = kurS12 a := by
  fin_cases a <;> decide

private theorem kurW_zero : kurW 0 = [(1 : Fin 3)] := rfl

private theorem kurW_succ (n : ℕ) : kurW (n + 1) =
    (List.map kurSigFn (kurW n) ++ kurW n) ++ List.map kurRhoFn (kurW n) := rfl

private theorem kurW_length (n : ℕ) : (kurW n).length = 3 ^ n := by
  induction n with
  | zero => simp [kurW_zero]
  | succ n ih =>
    rw [kurW_succ, List.length_append, List.length_append, List.length_map,
      List.length_map, ih, pow_succ]
    ring

private theorem kurW_get (n : ℕ) (k : ℕ) (hk : k < 3 ^ n) :
    (kurW n)[k]? = some ((kurS01 ^ n * kurGam k) (1 : Fin 3)) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by rw [pow_zero] at hk; omega
    subst hk0
    simp [kurW_zero, kurGam_zero]
  | succ n ih =>
    have hlen : (kurW n).length = 3 ^ n := kurW_length n
    have hlen1 : (List.map kurSigFn (kurW n)).length = 3 ^ n := by simp [hlen]
    have hlen2 : ((List.map kurSigFn (kurW n)) ++ kurW n).length = 2 * 3 ^ n := by
      rw [List.length_append, hlen1, hlen]; omega
    have hks : k < 3 ^ n * 3 := by rwa [pow_succ] at hk
    by_cases h1 : k < 3 ^ n
    · -- first third: sigma part
      have eapp : ((List.map kurSigFn (kurW n) ++ kurW n) ++
          List.map kurRhoFn (kurW n))[k]? =
          ((kurW n)[k]?).map kurSigFn := by
        rw [List.getElem?_append_left (by rw [hlen2]; omega),
          List.getElem?_append_left (by rw [hlen1]; omega), List.getElem?_map]
      rw [kurW_succ, eapp, ih _ h1]
      simp only [Option.map_some]
      rw [kurSigFn_eq]
      congr 1
      rw [pow_succ']
      simp [Equiv.Perm.mul_apply]
    · by_cases h2 : k < 2 * 3 ^ n
      · -- middle third
        have hk' : k - 3 ^ n < 3 ^ n := by omega
        have hkk : k = 3 ^ n + (k - 3 ^ n) := by omega
        have eapp : ((List.map kurSigFn (kurW n) ++ kurW n) ++
            List.map kurRhoFn (kurW n))[k]? = (kurW n)[k - 3 ^ n]? := by
          rw [List.getElem?_append_left (by rw [hlen2]; omega),
            List.getElem?_append_right (by rw [hlen1]; omega), hlen1]
        have eγ : kurGam k = kurS01 ^ n * kurS01 * kurS01 ^ n * kurGam (k - 3 ^ n) := by
          conv_lhs => rw [hkk]
          have hN := kurGam_top_digit n 1 (k - 3 ^ n) hk'
          rwa [one_mul, kurGam_one] at hN
        have hfin : kurS01 ^ (n + 1) * kurGam k = kurS01 ^ n * kurGam (k - 3 ^ n) := by
          rw [eγ]
          simp only [← mul_assoc]
          rw [kurS01_sq_mul, kurS01_sq, one_mul]
        rw [kurW_succ, eapp, ih _ hk', hfin]
      · -- last third: rho part
        have hk'' : k - 2 * 3 ^ n < 3 ^ n := by omega
        have hkk : k = 2 * 3 ^ n + (k - 2 * 3 ^ n) := by omega
        have eapp : ((List.map kurSigFn (kurW n) ++ kurW n) ++
            List.map kurRhoFn (kurW n))[k]? =
            (((kurW n)[k - 2 * 3 ^ n]?).map kurRhoFn) := by
          rw [List.getElem?_append_right (by rw [hlen2]; omega), hlen2,
            List.getElem?_map]
        have eγ : kurGam k = kurS01 ^ n * (kurS01 * kurS12) * kurS01 ^ n * kurGam
            (k - 2 * 3 ^ n) := by
          conv_lhs => rw [hkk]
          have hN := kurGam_top_digit n 2 (k - 2 * 3 ^ n) hk''
          rwa [kurGam_two] at hN
        have hfin : kurS01 ^ (n + 1) * kurGam k =
            kurS12 * (kurS01 ^ n * kurGam (k - 2 * 3 ^ n)) := by
          rw [eγ]
          simp only [← mul_assoc]
          rw [kurS01_sq_mul, kurS01_sq, one_mul]
        rw [kurW_succ, eapp, ih _ hk'']
        simp only [Option.map_some]
        rw [kurRhoFn_eq]
        congr 1
        rw [hfin]
        simp [Equiv.Perm.mul_apply]

/-- step(k) = γ(k)⁻¹·γ(k+1) -/
private def kurStep (k : ℕ) : Equiv.Perm (Fin 3) := (kurGam k)⁻¹ * kurGam (k + 1)

private theorem kurGam_step (k : ℕ) : kurGam (k + 1) = kurGam k * kurStep k := by
  change kurGam (k + 1) = kurGam k * ((kurGam k)⁻¹ * kurGam (k + 1))
  exact (mul_inv_cancel_left _ _).symm

private theorem kurS01_inv : kurS01⁻¹ = kurS01 := by
  have h := congrArg (kurS01⁻¹ * ·) kurS01_sq
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h
  exact h.symm

private theorem kurS12_sq' : kurS12 * kurS12 = 1 := Equiv.swap_mul_self 1 2

private theorem kurS12_inv : kurS12⁻¹ = kurS12 := by
  have h := congrArg (kurS12⁻¹ * ·) kurS12_sq'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h
  exact h.symm

private theorem kurTau_ge2 (d : ℕ) (h : 2 ≤ d) : kurTau d = kurS12 := by
  match d with
  | 0 => omega
  | 1 => omega
  | n + 1 + 1 => rfl

private theorem kurStep_three_mul (j : ℕ) : kurStep (3 * j) = kurS01 := by
  have e0 : kurGam (3 * j) = kurS01 * kurGam j * kurS01 := by
    have h := kurGam_three_mul_add j 0 (by omega)
    rwa [show 3 * j + 0 = 3 * j from by omega, kurTau_zero] at h
  have e1 : kurGam (3 * j + 1) = kurS01 * kurGam j := by
    have h := kurGam_three_mul_add j 1 (by omega)
    rwa [kurTau_one, mul_one] at h
  change (kurGam (3 * j))⁻¹ * kurGam (3 * j + 1) = _
  rw [e0, e1]
  calc (kurS01 * kurGam j * kurS01)⁻¹ * (kurS01 * kurGam j)
      = kurS01⁻¹ * ((kurS01 * kurGam j)⁻¹ * (kurS01 * kurGam j)) := by
        rw [mul_inv_rev, mul_assoc]
    _ = kurS01⁻¹ := by rw [inv_mul_cancel, mul_one]
    _ = kurS01 := kurS01_inv

private theorem kurStep_three_mul_add_one (j : ℕ) : kurStep (3 * j + 1) = kurS12 := by
  have e1 : kurGam (3 * j + 1) = kurS01 * kurGam j := by
    have h := kurGam_three_mul_add j 1 (by omega)
    rwa [kurTau_one, mul_one] at h
  have e2 : kurGam (3 * j + 2) = kurS01 * kurGam j * kurS12 := by
    have h := kurGam_three_mul_add j 2 (by omega)
    have h2 : kurTau 2 = kurS12 := kurTau_ge2 2 (by omega)
    rwa [h2] at h
  have e3 : kurGam (3 * j + 1 + 1) = kurS01 * kurGam j * kurS12 := by
    have : 3 * j + 1 + 1 = 3 * j + 2 := by omega
    rwa [this]
  change (kurGam (3 * j + 1))⁻¹ * kurGam (3 * j + 1 + 1) = _
  rw [e1, e3]
  calc (kurS01 * kurGam j)⁻¹ * (kurS01 * kurGam j * kurS12)
      = ((kurS01 * kurGam j)⁻¹ * (kurS01 * kurGam j)) * kurS12 := by
        rw [← mul_assoc]
    _ = kurS12 := by rw [inv_mul_cancel, one_mul]

private theorem kurS12_cancel (X : Equiv.Perm (Fin 3)) : kurS12 * (kurS12 * X) = X := by
  rw [← mul_assoc, kurS12_sq', one_mul]

private theorem kurStep_mem : ∀ k : ℕ, kurStep k = kurS01 ∨ kurStep k = kurS12 := by
  intro k
  exact Nat.strong_induction_on k (fun k ih => by
    have hmod : k % 3 < 3 := Nat.mod_lt _ (by omega)
    have hsplit : k = 3 * (k / 3) + k % 3 := (Nat.div_add_mod k 3).symm
    match he : k % 3 with
    | 0 =>
      have hk : k = 3 * (k / 3) := by omega
      rw [hk]
      exact Or.inl (kurStep_three_mul _)
    | 1 =>
      have hk : k = 3 * (k / 3) + 1 := by omega
      rw [hk]
      exact Or.inr (kurStep_three_mul_add_one _)
    | 2 =>
      have hk : k = 3 * (k / 3) + 2 := by omega
      have hj : k / 3 < k := by omega
      have e2 : kurGam k = kurS01 * kurGam (k / 3) * kurS12 := by
        have h := kurGam_three_mul_add (k / 3) 2 (by omega)
        have h2 : kurTau 2 = kurS12 := kurTau_ge2 2 (by omega)
        rw [h2] at h
        conv_lhs => rw [hk]
        exact h
      have e3 : kurGam (k + 1) = kurS01 * (kurGam (k / 3) * kurStep (k / 3)) * kurS01 := by
        have h := kurGam_three_mul_add (k / 3 + 1) 0 (by omega)
        rw [kurTau_zero] at h
        rw [kurGam_step (k / 3)] at h
        have hkk : k + 1 = 3 * (k / 3 + 1) + 0 := by omega
        conv_lhs => rw [hkk]
        exact h
      have estep : kurStep k =
          (kurS01 * kurGam (k / 3) * kurS12)⁻¹ *
          (kurS01 * (kurGam (k / 3) * kurStep (k / 3)) * kurS01) := by
        change (kurGam k)⁻¹ * kurGam (k + 1) = _
        rw [e2, e3]
      have key : (kurS01 * kurGam (k / 3) * kurS12)⁻¹ *
          (kurS01 * (kurGam (k / 3) * kurStep (k / 3)) * kurS01)
          = kurS12 * kurStep (k / 3) * kurS01 := by
        have hcancel : (kurS01 * kurGam (k / 3) * kurS12) *
            ((kurS01 * kurGam (k / 3) * kurS12)⁻¹ *
              (kurS01 * (kurGam (k / 3) * kurStep (k / 3)) * kurS01))
            = (kurS01 * kurGam (k / 3) * kurS12) * (kurS12 * kurStep (k / 3) * kurS01) := by
          rw [mul_inv_cancel_left]
          simp only [mul_assoc]
          rw [kurS12_cancel]
        exact mul_left_cancel hcancel
      rw [estep, key]
      rcases ih (k / 3) hj with hs | hs
      · rw [hs, mul_assoc, kurS01_sq, mul_one]
        exact Or.inr rfl
      · rw [hs, kurS12_sq', one_mul]
        exact Or.inl rfl
    | _ + 3 => omega)

-- finite facts
private theorem kurStep01_ne : kurS01 ≠ kurS12 :=
  fun h => (by decide : kurS01 (0 : Fin 3) ≠ kurS12 (0 : Fin 3)) (congrArg (· 0) h)

private theorem kurStep01_ne_one : kurS01 ≠ 1 :=
  fun h => (by decide : kurS01 (0 : Fin 3) ≠ (1 : Equiv.Perm (Fin 3)) (0 : Fin 3))
    (congrArg (· 0) h)

private theorem kurStep12_ne_one : kurS12 ≠ 1 :=
  fun h => (by decide : kurS12 (1 : Fin 3) ≠ (1 : Equiv.Perm (Fin 3)) (1 : Fin 3))
    (congrArg (· 1) h)

private theorem kurStep01_mul_12_ne_one : kurS01 * kurS12 ≠ 1 :=
  fun h => (by decide : ((kurS01 * kurS12) (0 : Fin 3)) ≠ ((1 : Equiv.Perm (Fin 3)) (0 : Fin 3)))
    (congrArg (· 0) h)

private theorem kurStep12_mul_01_ne_one : kurS12 * kurS01 ≠ 1 :=
  fun h => (by decide : ((kurS12 * kurS01) (1 : Fin 3)) ≠ ((1 : Equiv.Perm (Fin 3)) (1 : Fin 3)))
    (congrArg (· 1) h)

private theorem kurStep_eq_of_next {a q : ℕ} (h1 : kurGam a = kurGam (a + q))
    (h2 : kurGam (a + 1) = kurGam (a + 1 + q)) : kurStep a = kurStep (a + q) := by
  have e : (a + q) + 1 = a + 1 + q := by omega
  unfold kurStep
  rw [h1, e, h2]

private theorem kurGam_rep_transfer {s m r k d t : ℕ}
    (hG : ∀ i, i + 3 * r < m → kurGam (s + i) = kurGam (s + i + 3 * r))
    (htd : t = 3 * k + d) (hd : d < 3) (hst : s ≤ t) (htm : t + 3 * r < s + m) :
    kurGam k = kurGam (k + r) := by
  have h1 : kurGam (3 * k + d) = kurGam (3 * (k + r) + d) := by
    have h := hG (t - s) (by omega)
    have e1 : s + (t - s) = 3 * k + d := by omega
    have e2 : s + (t - s) + 3 * r = 3 * (k + r) + d := by omega
    rwa [e2, e1] at h
  rw [kurGam_three_mul_add k d hd, kurGam_three_mul_add (k + r) d hd] at h1
  simp only [mul_assoc] at h1
  exact mul_right_cancel (mul_left_cancel h1)

private theorem kurGam_rep_desubst (r s m : ℕ) (hr : 1 ≤ r) (hm : 3 * r < m)
    (hG : ∀ i, i + 3 * r < m → kurGam (s + i) = kurGam (s + i + 3 * r)) :
    (∀ i, i + r < (s + m - 1) / 3 - s / 3 + 1 → kurGam (s / 3 + i) = kurGam (s / 3 + i + r))
    ∧ m ≤ 3 * ((s + m - 1) / 3 - s / 3 + 1) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have ha1 : 3 * (s / 3) ≤ s := by omega
    have ha2 : s < 3 * (s / 3) + 3 := by omega
    rcases le_total (3 * (s / 3 + i)) s with hle | hle
    · have hd : s - 3 * (s / 3 + i) < 3 := by omega
      have htd : s = 3 * (s / 3 + i) + (s - 3 * (s / 3 + i)) := by omega
      have htm : s + 3 * r < s + m := by omega
      exact kurGam_rep_transfer hG htd hd (le_refl s) htm
    · have hMpos : s / 3 ≤ (s + m - 1) / 3 := by omega
      have hi2 : i + r + s / 3 ≤ (s + m - 1) / 3 := by omega
      have htm : 3 * (s / 3 + i) + 3 * r < s + m := by omega
      exact kurGam_rep_transfer hG
        (show 3 * (s / 3 + i) = 3 * (s / 3 + i) + 0 by omega)
        (show (0 : ℕ) < 3 by omega) hle htm
  · have hAge : s / 3 ≤ (s + m - 1) / 3 := by omega
    have h1 : s + m - 3 ≤ 3 * ((s + m - 1) / 3) := by omega
    have h2 : 3 * (s / 3) ≤ s := by omega
    omega

private theorem kurGam_rep_short (q s m : ℕ) (_hq : 1 ≤ q) (hq3 : q % 3 ≠ 0)
    (hG : ∀ i, i + q < m → kurGam (s + i) = kurGam (s + i + q)) :
    m ≤ q + 3 := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j, j ≤ 2 → kurStep (s + j) = kurStep (s + j + q) := by
    intro j hj
    exact kurStep_eq_of_next (hG j (by omega)) (hG (j + 1) (by omega))
  have hqm : q % 3 = 1 ∨ q % 3 = 2 := by
    have h := Nat.mod_lt q (by omega : 0 < 3)
    omega
  rcases hqm with hq1mod | hq2mod
  · obtain ⟨j, hj2, hjm⟩ : ∃ j, j ≤ 2 ∧ (s + j) % 3 = 0 := by
      have hs : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by
        have h := Nat.mod_lt s (by omega : 0 < 3)
        omega
      rcases hs with hs | hs | hs
      · exact ⟨0, by omega, by omega⟩
      · exact ⟨2, by omega, by omega⟩
      · exact ⟨1, by omega, by omega⟩
    have hs1 : kurStep (s + j) = kurS01 := by
      have hjj : s + j = 3 * ((s + j) / 3) := by omega
      rw [hjj]
      exact kurStep_three_mul _
    have hs2 : kurStep (s + j + q) = kurS12 := by
      have hmod : (s + j + q) % 3 = 1 := by omega
      have hjj : s + j + q = 3 * ((s + j + q) / 3) + 1 := by omega
      rw [hjj]
      exact kurStep_three_mul_add_one _
    have hst := hstep j hj2
    rw [hs1, hs2] at hst
    exact kurStep01_ne hst
  · obtain ⟨j, hj2, hjm⟩ : ∃ j, j ≤ 2 ∧ (s + j) % 3 = 1 := by
      have hs : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by
        have h := Nat.mod_lt s (by omega : 0 < 3)
        omega
      rcases hs with hs | hs | hs
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
      · exact ⟨2, by omega, by omega⟩
    have hs1 : kurStep (s + j) = kurS12 := by
      have hjj : s + j = 3 * ((s + j) / 3) + 1 := by omega
      rw [hjj]
      exact kurStep_three_mul_add_one _
    have hs2 : kurStep (s + j + q) = kurS01 := by
      have hmod : (s + j + q) % 3 = 0 := by omega
      have hjj : s + j + q = 3 * ((s + j + q) / 3) := by omega
      rw [hjj]
      exact kurStep_three_mul _
    have hst := hstep j hj2
    rw [hs1, hs2] at hst
    exact kurStep01_ne hst.symm

private theorem kurGam_rep_one (s m : ℕ)
    (hG : ∀ i, i + 1 < m → kurGam (s + i) = kurGam (s + i + 1)) : m ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : kurGam s = kurGam (s + 1) := hG 0 (by omega)
  have hcon2 : kurStep s = 1 := by
    have e := kurGam_step s
    have hcc : kurGam s * kurStep s = kurGam s * 1 := by
      rw [mul_one]
      exact e.symm.trans h0.symm
    exact mul_left_cancel hcc
  rcases kurStep_mem s with hs | hs
  · rw [hs] at hcon2; exact kurStep01_ne_one hcon2
  · rw [hs] at hcon2; exact kurStep12_ne_one hcon2

private theorem kurGam_rep_two (s m : ℕ)
    (hG : ∀ i, i + 2 < m → kurGam (s + i) = kurGam (s + i + 2)) : m ≤ 3 := by
  by_contra hcon
  push Not at hcon
  have g0 : kurGam s = kurGam (s + 2) := hG 0 (by omega)
  have g1 : kurGam (s + 1) = kurGam (s + 3) := hG 1 (by omega)
  have cS : kurGam (s + 2) = kurGam (s + 1) * kurStep (s + 1) := kurGam_step (s + 1)
  have cS2 : kurGam (s + 3) = kurGam (s + 2) * kurStep (s + 2) := kurGam_step (s + 2)
  have eA : kurGam (s + 2) = kurGam s * (kurStep s * kurStep (s + 1)) := by
    rw [cS, kurGam_step s, mul_assoc]
  have eB : kurGam (s + 3) = kurGam (s + 1) * (kurStep (s + 1) * kurStep (s + 2)) := by
    rw [cS2, cS, mul_assoc]
  have eprod1 : kurStep s * kurStep (s + 1) = 1 := by
    have hcancel : kurGam s * (kurStep s * kurStep (s + 1)) = kurGam s * 1 := by
      rw [mul_one, ← eA, g0]
    exact mul_left_cancel hcancel
  have eprod2 : kurStep (s + 1) * kurStep (s + 2) = 1 := by
    have hcancel : kurGam (s + 1) * (kurStep (s + 1) * kurStep (s + 2))
        = kurGam (s + 1) * 1 := by
      rw [mul_one, ← eB, g1]
    exact mul_left_cancel hcancel
  have estep1 : kurStep s = kurStep (s + 1) := by
    rcases kurStep_mem s with hs | hs <;> rcases kurStep_mem (s + 1) with hs1 | hs1
    · rw [hs, hs1]
    · exfalso; rw [hs, hs1] at eprod1; exact kurStep01_mul_12_ne_one eprod1
    · exfalso; rw [hs, hs1] at eprod1; exact kurStep12_mul_01_ne_one eprod1
    · rw [hs, hs1]
  have estep2 : kurStep (s + 1) = kurStep (s + 2) := by
    rcases kurStep_mem (s + 1) with hs | hs <;> rcases kurStep_mem (s + 2) with hs1 | hs1
    · rw [hs, hs1]
    · exfalso; rw [hs, hs1] at eprod2; exact kurStep01_mul_12_ne_one eprod2
    · exfalso; rw [hs, hs1] at eprod2; exact kurStep12_mul_01_ne_one eprod2
    · rw [hs, hs1]
  have hs3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by
    have h := Nat.mod_lt s (by omega : 0 < 3)
    omega
  rcases hs3 with hs | hs | hs
  · have v0 : kurStep s = kurS01 := by
      have h : s = 3 * (s / 3) := by omega
      rw [h]; exact kurStep_three_mul _
    have v1 : kurStep (s + 1) = kurS12 := by
      have h : s + 1 = 3 * ((s + 1) / 3) + 1 := by omega
      rw [h]; exact kurStep_three_mul_add_one _
    rw [v0, v1] at estep1
    exact kurStep01_ne estep1
  · have v0 : kurStep s = kurS12 := by
      have h : s = 3 * (s / 3) + 1 := by omega
      rw [h]; exact kurStep_three_mul_add_one _
    have v2 : kurStep (s + 2) = kurS01 := by
      have h : s + 2 = 3 * ((s + 2) / 3) := by omega
      rw [h]; exact kurStep_three_mul _
    rw [v2] at estep2
    rw [v0, estep2] at estep1
    exact kurStep01_ne estep1.symm
  · have v1 : kurStep (s + 1) = kurS01 := by
      have h : s + 1 = 3 * ((s + 1) / 3) := by omega
      rw [h]; exact kurStep_three_mul _
    have v2 : kurStep (s + 2) = kurS12 := by
      have h : s + 2 = 3 * ((s + 2) / 3) + 1 := by omega
      rw [h]; exact kurStep_three_mul_add_one _
    rw [v1, v2] at estep2
    exact kurStep01_ne estep2

private theorem kurGam_rep_bound : ∀ q s m : ℕ, 1 ≤ q →
    (∀ i, i + q < m → kurGam (s + i) = kurGam (s + i + q)) → 4 * m ≤ 7 * q := by
  intro q
  exact Nat.strong_induction_on q (fun q ih s m hq hG => by
    by_cases hmle : m ≤ q
    · omega
    · push Not at hmle
      by_cases hq0 : q % 3 = 0
      · have hqr : q = 3 * (q / 3) := by omega
        have hr1 : 1 ≤ q / 3 := by omega
        have hrq : q / 3 < q := by omega
        have h3r : 3 * (q / 3) < m := by omega
        have hG' : ∀ i, i + 3 * (q / 3) < m → kurGam (s + i) = kurGam (s + i + 3 * (q / 3)) := by
          intro i hi
          have hiq : i + q < m := by omega
          have h := hG i hiq
          rwa [hqr] at h
        obtain ⟨hGM, hmM⟩ := kurGam_rep_desubst (q / 3) s m hr1 h3r hG'
        have ihM := ih (q / 3) hrq (s / 3) ((s + m - 1) / 3 - s / 3 + 1) hr1 hGM
        omega
      · have hm3 := kurGam_rep_short q s m hq hq0 hG
        by_cases hq1 : q = 1
        · subst hq1
          have hm1 := kurGam_rep_one s m hG
          omega
        · by_cases hq2 : q = 2
          · subst hq2
            have hm2 := kurGam_rep_two s m hG
            omega
          · have hq4 : 4 ≤ q := by
              have h := Nat.mod_lt q (by omega : 0 < 3)
              omega
            omega)

/-- N8(a): two agreeing letters determine a permutation of `Fin 3`. -/
private theorem kurPerm3_twopt : ∀ a b : Equiv.Perm (Fin 3), ∀ x y : Fin 3,
    x ≠ y → a x = b x → a y = b y → a = b := by decide

/-- N8(b): left-boundary lift through a step in {σ, ρ}. -/
private theorem kurPerm3_liftL : ∀ a b D D' : Equiv.Perm (Fin 3), ∀ x : Fin 3,
    (D = kurS01 ∨ D = kurS12) → (D' = kurS01 ∨ D' = kurS12) →
    a * D = b * D' → a x = b x → a = b := by decide

/-- N8(c): one letter determines the step in {σ, ρ}. -/
private theorem kurPerm3_stepdet : ∀ a D D' : Equiv.Perm (Fin 3), ∀ x : Fin 3,
    (D = kurS01 ∨ D = kurS12) → (D' = kurS01 ∨ D' = kurS12) →
    (a * D) x = (a * D') x → D = D' := by decide

/-- The six possible 3-blocks. -/
private def kurPerms6 : List (List (Fin 3)) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

private theorem kurPerm3_mem6 : ∀ g : Equiv.Perm (Fin 3), [g 0, g 1, g 2] ∈ kurPerms6 := by decide

/-- ω, the infinite ternary word: ω(k) = γ(k)(1). -/
private def kurWord (k : ℕ) : Fin 3 := kurGam k 1

/-- ORep(s, m, p): ω agrees with its p-shift on the window starting at s. -/
private def ORep (s m p : ℕ) : Prop :=
  ∀ i : ℕ, i + p < m → kurWord (s + i) = kurWord (s + i + p)

private theorem kurTau_apply_one (d : Fin 3) : kurTau d.val 1 = d := by
  fin_cases d <;> decide

/-- N9(i): block formula. -/
private theorem kurWord_block (k : ℕ) (d : Fin 3) :
    kurWord (3 * k + d.val) = kurS01 (kurGam k d) := by
  have h := kurGam_three_mul_add k d.val d.2
  change kurGam (3 * k + d.val) 1 = _
  rw [h, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, kurTau_apply_one d]

/-- Two in-range positions in one 3-block force γ(k) = γ(k+q). -/
private theorem kurWord_two_pos {q s m : ℕ}
    (hrep : ∀ t : ℕ, s ≤ t → t + 3 * q < s + m → kurWord t = kurWord (t + 3 * q))
    (k d₁ d₂ : ℕ) (hd₁ : d₁ < 3) (hd₂ : d₂ < 3) (hne : d₁ ≠ d₂)
    (h₁ : s ≤ 3 * k + d₁) (h₁' : 3 * k + d₁ + 3 * q < s + m)
    (h₂ : s ≤ 3 * k + d₂) (h₂' : 3 * k + d₂ + 3 * q < s + m) :
    kurGam k = kurGam (k + q) := by
  have e₁ := hrep (3 * k + d₁) h₁ h₁'
  have e₂ := hrep (3 * k + d₂) h₂ h₂'
  have b₁ : kurWord (3 * k + d₁) = kurS01 (kurGam k ⟨d₁, hd₁⟩) :=
    kurWord_block k ⟨d₁, hd₁⟩
  have b₂ : kurWord (3 * k + d₂) = kurS01 (kurGam k ⟨d₂, hd₂⟩) :=
    kurWord_block k ⟨d₂, hd₂⟩
  have ee₁ : 3 * k + d₁ + 3 * q = 3 * (k + q) + d₁ := by omega
  have ee₂ : 3 * k + d₂ + 3 * q = 3 * (k + q) + d₂ := by omega
  have b₁' : kurWord (3 * (k + q) + d₁) = kurS01 (kurGam (k + q) ⟨d₁, hd₁⟩) :=
    kurWord_block (k + q) ⟨d₁, hd₁⟩
  have b₂' : kurWord (3 * (k + q) + d₂) = kurS01 (kurGam (k + q) ⟨d₂, hd₂⟩) :=
    kurWord_block (k + q) ⟨d₂, hd₂⟩
  rw [b₁, ee₁, b₁'] at e₁
  rw [b₂, ee₂, b₂'] at e₂
  have c₁ : kurGam k ⟨d₁, hd₁⟩ = kurGam (k + q) ⟨d₁, hd₁⟩ :=
    (Equiv.apply_eq_iff_eq _).mp e₁
  have c₂ : kurGam k ⟨d₂, hd₂⟩ = kurGam (k + q) ⟨d₂, hd₂⟩ :=
    (Equiv.apply_eq_iff_eq _).mp e₂
  have hne' : (⟨d₁, hd₁⟩ : Fin 3) ≠ ⟨d₂, hd₂⟩ := by
    intro hcon
    exact hne (congrArg Fin.val hcon)
  exact kurPerm3_twopt _ _ _ _ hne' c₁ c₂

/-- N9(ii): lift an ω-repetition of period 3q to a γ-repetition of period q. -/
private theorem kurWord_rep_lift (q s m : ℕ) (_hq : 1 ≤ q) (hm : 3 * q + 3 ≤ m)
    (h : ORep s m (3 * q)) :
    (∀ i, i + q < (s + (m - 3 * q) - 1) / 3 - s / 3 + 1 + q →
      kurGam (s / 3 + i) = kurGam (s / 3 + i + q)) ∧
    m ≤ 3 * ((s + (m - 3 * q) - 1) / 3 - s / 3 + 1 + q) := by
  have hℓ : m = (m - 3 * q) + 3 * q := by omega
  have hℓ3 : 3 ≤ m - 3 * q := by omega
  have hs := Nat.div_add_mod s 3
  have hsb := Nat.div_add_mod (s + (m - 3 * q) - 1) 3
  have hrep : ∀ t : ℕ, s ≤ t → t + 3 * q < s + m → kurWord t = kurWord (t + 3 * q) := by
    intro t hst htm
    have hj : t - s + 3 * q < m := by omega
    have hh := h (t - s) hj
    have hts : s + (t - s) = t := by omega
    rwa [hts] at hh
  refine ⟨?_, ?_⟩
  · intro i hi
    set a := s / 3 with ha
    set b := (s + (m - 3 * q) - 1) / 3 with hb
    set k := a + i with hk
    have hka : a ≤ k := by omega
    have hkb : k ≤ b := by omega
    have hcases : (s ≤ 3 * k ∧ 3 * k + 1 < s + (m - 3 * q)) ∨
        (s ≤ 3 * k + 1 ∧ 3 * k + 2 < s + (m - 3 * q)) ∨
        (k = a ∧ s = 3 * a + 2) ∨ (k = b ∧ s + (m - 3 * q) - 1 = 3 * b) := by
      omega
    rcases hcases with ⟨hL1, hR1⟩ | ⟨hL2, hR2⟩ | ⟨hka2, hs2⟩ | ⟨hkb2, hsb2⟩
    · exact kurWord_two_pos hrep k 0 1 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · exact kurWord_two_pos hrep k 1 2 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · -- left boundary: only position 3a+2 meets the range
      have hd2 : (2 : ℕ) < 3 := by omega
      have hv2 : ((⟨2, hd2⟩ : Fin 3).val) = 2 := rfl
      have gmid : kurGam (a + 1) = kurGam (a + 1 + q) :=
        kurWord_two_pos hrep (a + 1) 0 1 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)
      have hspos : kurWord s = kurWord (s + 3 * q) := hrep s (le_refl s) (by omega)
      have hbb := kurWord_block a ⟨2, hd2⟩
      rw [hv2, show 3 * a + 2 = s from by omega] at hbb
      have hbb2 := kurWord_block (a + q) ⟨2, hd2⟩
      rw [hv2, show 3 * (a + q) + 2 = s + 3 * q from by omega] at hbb2
      rw [hbb, hbb2] at hspos
      have c2 : kurGam a ⟨2, hd2⟩ = kurGam (a + q) ⟨2, hd2⟩ :=
        (Equiv.apply_eq_iff_eq _).mp hspos
      have estep : kurGam a * kurStep a = kurGam (a + q) * kurStep (a + q) := by
        have g1 := kurGam_step a
        have g2 := kurGam_step (a + q)
        have e : a + 1 + q = a + q + 1 := by omega
        rw [e] at gmid
        rw [← g1, ← g2]
        exact gmid
      have hfin : kurGam a = kurGam (a + q) :=
        kurPerm3_liftL _ _ _ _ _ (kurStep_mem a) (kurStep_mem (a + q)) estep c2
      rw [hka2]
      exact hfin
    · -- right boundary: only position 3b meets the range
      have hd0 : (0 : ℕ) < 3 := by omega
      have hv0 : ((⟨0, hd0⟩ : Fin 3).val) = 0 := rfl
      have hb1 : 1 ≤ b := by omega
      have hb1' : b - 1 + 1 = b := by omega
      have gmid : kurGam (b - 1) = kurGam (b - 1 + q) :=
        kurWord_two_pos hrep (b - 1) 1 2 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)
      have h3b : kurWord (3 * b) = kurWord (3 * b + 3 * q) :=
        hrep (3 * b) (by omega) (by omega)
      have hcc := kurWord_block b ⟨0, hd0⟩
      rw [hv0, show 3 * b + 0 = 3 * b from by omega] at hcc
      have hcc2 := kurWord_block (b + q) ⟨0, hd0⟩
      rw [hv0, show 3 * (b + q) + 0 = 3 * b + 3 * q from by omega] at hcc2
      rw [hcc, hcc2] at h3b
      have c0 : kurGam b ⟨0, hd0⟩ = kurGam (b + q) ⟨0, hd0⟩ :=
        (Equiv.apply_eq_iff_eq _).mp h3b
      have e1 := kurGam_step (b - 1)
      rw [hb1'] at e1
      have e2 := kurGam_step (b - 1 + q)
      have he2 : b - 1 + q + 1 = b + q := by omega
      rw [he2] at e2
      rw [e1, e2, ← gmid] at c0
      have hstep : kurStep (b - 1) = kurStep (b - 1 + q) :=
        kurPerm3_stepdet _ _ _ _ (kurStep_mem _) (kurStep_mem _) c0
      have hfin : kurGam b = kurGam (b + q) := by
        rw [e1, e2, ← gmid, hstep]
      rw [hkb2]
      exact hfin
  · omega

/-- The 3-block of ω at k. -/
private def kurBlock (k : ℕ) : List (Fin 3) :=
  [kurWord (3 * k), kurWord (3 * k + 1), kurWord (3 * k + 2)]

/-- Step bit: true iff the step is ρ. -/
private def kurStepBit (k : ℕ) : Bool := decide (kurStep k = kurS12)

/-- How a step transforms a block. -/
private def kurStepBlock : Bool → List (Fin 3) → List (Fin 3)
  | false, [x, y, z] => [y, x, z]
  | true, [x, y, z] => [x, z, y]
  | _, l => l

/-- Step bits from k to k+K-1. -/
private def kurBits : ℕ → ℕ → List Bool
  | _, 0 => []
  | k, K + 1 => kurStepBit k :: kurBits (k + 1) K

/-- Local model of a 3(K+1)-letter window of ω. -/
private def kurModelWin : List (Fin 3) → List Bool → List (Fin 3)
  | b, [] => b
  | b, t :: ts => b ++ kurModelWin (kurStepBlock t b) ts

/-- Step-pattern validity. -/
private def kurPatternOK (e : ℕ) (ts : List Bool) : Bool :=
  List.all (List.range ts.length) (fun i =>
    if (e + i) % 3 = 0 then ts[i]? == some false
    else if (e + i) % 3 = 1 then ts[i]? == some true else true)

private theorem kurBlock_eq (k : ℕ) :
    kurBlock k = [kurS01 (kurGam k 0), kurS01 (kurGam k 1), kurS01 (kurGam k 2)] := by
  change [kurWord (3 * k), kurWord (3 * k + 1), kurWord (3 * k + 2)] = _
  rw [show kurWord (3 * k) = kurS01 (kurGam k 0) from kurWord_block k 0,
    show kurWord (3 * k + 1) = kurS01 (kurGam k 1) from kurWord_block k 1,
    show kurWord (3 * k + 2) = kurS01 (kurGam k 2) from kurWord_block k 2]

private theorem kurStepBit_false {t : ℕ} (h : kurStep t = kurS01) : kurStepBit t = false := by
  change decide (kurStep t = kurS12) = false
  rw [h]
  decide

private theorem kurStepBit_true {t : ℕ} (h : kurStep t = kurS12) : kurStepBit t = true := by
  change decide (kurStep t = kurS12) = true
  rw [h]
  decide

private theorem kurStepBlock_block (k : ℕ) :
    kurStepBlock (kurStepBit k) (kurBlock k) = kurBlock (k + 1) := by
  have step_eq : ∀ d : Fin 3, kurGam (k + 1) d = kurGam k (kurStep k d) := by
    intro d
    rw [kurGam_step k, Equiv.Perm.mul_apply]
  rcases kurStep_mem k with hs | hs
  · have hb := kurStepBit_false hs
    have s0 : kurS01 (0 : Fin 3) = 1 := by decide
    have s1 : kurS01 (1 : Fin 3) = 0 := by decide
    have s2 : kurS01 (2 : Fin 3) = 2 := by decide
    have r0 : kurGam (k + 1) (0 : Fin 3) = kurGam k 1 := by rw [step_eq, hs, s0]
    have r1 : kurGam (k + 1) (1 : Fin 3) = kurGam k 0 := by rw [step_eq, hs, s1]
    have r2 : kurGam (k + 1) (2 : Fin 3) = kurGam k 2 := by rw [step_eq, hs, s2]
    rw [hb, kurBlock_eq k, kurBlock_eq (k + 1)]
    change [kurS01 (kurGam k 1), kurS01 (kurGam k 0), kurS01 (kurGam k 2)] =
      [kurS01 (kurGam (k + 1) 0), kurS01 (kurGam (k + 1) 1), kurS01 (kurGam (k + 1) 2)]
    rw [r0, r1, r2]
  · have hb := kurStepBit_true hs
    have r0 : kurS12 (0 : Fin 3) = 0 := by decide
    have r1 : kurS12 (1 : Fin 3) = 2 := by decide
    have r2 : kurS12 (2 : Fin 3) = 1 := by decide
    have g0 : kurGam (k + 1) (0 : Fin 3) = kurGam k 0 := by rw [step_eq, hs, r0]
    have g1 : kurGam (k + 1) (1 : Fin 3) = kurGam k 2 := by rw [step_eq, hs, r1]
    have g2 : kurGam (k + 1) (2 : Fin 3) = kurGam k 1 := by rw [step_eq, hs, r2]
    rw [hb, kurBlock_eq k, kurBlock_eq (k + 1)]
    change [kurS01 (kurGam k 0), kurS01 (kurGam k 2), kurS01 (kurGam k 1)] =
      [kurS01 (kurGam (k + 1) 0), kurS01 (kurGam (k + 1) 1), kurS01 (kurGam (k + 1) 2)]
    rw [g0, g1, g2]

private theorem kurBits_length (k K : ℕ) : (kurBits k K).length = K := by
  induction K generalizing k with
  | zero => rfl
  | succ K ih =>
    change (kurStepBit k :: kurBits (k + 1) K).length = K + 1
    rw [List.length_cons, ih]

private theorem kurBits_get (k K i : ℕ) (hi : i < K) :
    (kurBits k K)[i]? = some (kurStepBit (k + i)) := by
  induction K generalizing k i with
  | zero => omega
  | succ K ih =>
    change (kurStepBit k :: kurBits (k + 1) K)[i]? = some (kurStepBit (k + i))
    by_cases h0 : i = 0
    · subst h0
      change some (kurStepBit k) = some (kurStepBit (k + 0))
      rw [Nat.add_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [List.getElem?_cons_succ]
      have hmem := ih (k + 1) j (by omega)
      have e : k + 1 + j = k + (j + 1) := by omega
      rwa [e] at hmem

/-- N10(a): the model window matches ω. -/
private theorem kurWord_window (k K : ℕ) :
    (kurModelWin (kurBlock k) (kurBits k K)).length = 3 * (K + 1) ∧
    ∀ j : ℕ, j < 3 * (K + 1) →
      (kurModelWin (kurBlock k) (kurBits k K))[j]? = some (kurWord (3 * k + j)) := by
  induction K generalizing k with
  | zero =>
    have hlen3 : (kurBlock k).length = 3 := rfl
    change (kurBlock k).length = 3 * (0 + 1) ∧
      ∀ j : ℕ, j < 3 * (0 + 1) → (kurBlock k)[j]? = some (kurWord (3 * k + j))
    refine ⟨by omega, ?_⟩
    intro j hj
    have hj3 : j < 3 := by omega
    interval_cases j <;> rfl
  | succ K ih =>
    have ihk1 := ih (k + 1)
    have hlen3 : (kurBlock k).length = 3 := rfl
    have hstep := kurStepBlock_block k
    have hbits : kurBits k (K + 1) = kurStepBit k :: kurBits (k + 1) K := rfl
    have hmod : kurModelWin (kurBlock k) (kurStepBit k :: kurBits (k + 1) K) =
        (kurBlock k) ++
          kurModelWin (kurStepBlock (kurStepBit k) (kurBlock k)) (kurBits (k + 1) K) :=
      rfl
    rw [hbits, hmod, hstep]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ihk1.1, hlen3]
      omega
    · intro j hj
      by_cases hj3 : j < 3
      · rw [List.getElem?_append_left (by rw [hlen3]; exact hj3)]
        have hj3' : j < 3 := hj3
        interval_cases j <;> rfl
      · have hbound : (kurBlock k).length ≤ j := by rw [hlen3]; omega
        rw [List.getElem?_append_right hbound, hlen3]
        have hIH := ihk1.2 (j - 3) (by omega)
        rwa [show 3 * (k + 1) + (j - 3) = 3 * k + j from by omega] at hIH

/-- N10(b): the step bits satisfy the pattern. -/
private theorem kurPatternOK_bits (k K : ℕ) : kurPatternOK (k % 3) (kurBits k K) = true := by
  simp only [kurPatternOK, List.all_eq_true]
  intro i hi
  rw [List.mem_range, kurBits_length] at hi
  show (if (k % 3 + i) % 3 = 0 then (kurBits k K)[i]? == some false
    else if (k % 3 + i) % 3 = 1 then (kurBits k K)[i]? == some true else true) = true
  rw [kurBits_get k K i hi, show (k % 3 + i) % 3 = (k + i) % 3 from by omega]
  have hki : (k + i) % 3 = 0 ∨ (k + i) % 3 = 1 ∨ (k + i) % 3 = 2 := by
    have h := Nat.mod_lt (k + i) (by omega : 0 < 3)
    omega
  rcases hki with h0 | h1 | h2
  · rw [ite_eq_left h0]
    have hstep : kurStep (k + i) = kurS01 := by
      have e : k + i = 3 * ((k + i) / 3) := by
        have hdm := Nat.div_add_mod (k + i) 3
        omega
      rw [e]
      exact kurStep_three_mul _
    rw [kurStepBit_false hstep]
    rfl
  · rw [ite_eq_right (by omega), ite_eq_left h1]
    have hstep : kurStep (k + i) = kurS12 := by
      have e : k + i = 3 * ((k + i) / 3) + 1 := by
        have hdm := Nat.div_add_mod (k + i) 3
        omega
      rw [e]
      exact kurStep_three_mul_add_one _
    rw [kurStepBit_true hstep]
    rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- N10(c): every block is one of the six permutations. -/
private theorem kurBlock_mem (k : ℕ) : kurBlock k ∈ kurPerms6 := by
  have h := kurPerm3_mem6 (kurS01 * kurGam k)
  have e : kurBlock k = [(kurS01 * kurGam k) 0, (kurS01 * kurGam k) 1,
      (kurS01 * kurGam k) 2] := by
    rw [kurBlock_eq]
    simp only [Equiv.Perm.mul_apply]
  rw [e]
  exact h

/-- Mark of a position: agreement at +2 (weight 1) and +3 (weight 2). -/
private def kurMark (x : List (Fin 3)) (i : ℕ) : ℕ :=
  (if x[i]? = x[i + 2]? then 1 else 0) + (if x[i]? = x[i + 3]? then 2 else 0)

/-- Phase detection on a 9-letter window. -/
private def kurPhase9 (x : List (Fin 3)) : ℕ :=
  match [1, 2, 3, 4, 5].find? (fun i => kurMark x i != (kurMark x (i - 1) + 1) % 3) with
  | some i => (3 - i % 3) % 3
  | none => 0

/-- N11(a): finite synchronization table. -/
private def kurSyncCheck : Bool :=
  decide (∀ b ∈ kurPerms6, ∀ e ∈ List.range 3, ∀ t0 t1 t2 : Bool,
    kurPatternOK e [t0, t1, t2] = true → ∀ d ∈ List.range 3,
    kurPhase9 (((kurModelWin b [t0, t1, t2]).drop d).take 9) = d)

private theorem kurWord_sync_table : kurSyncCheck = true := by decide

private theorem kurSyncCheck_apply (b : List (Fin 3)) (e : ℕ) (t0 t1 t2 : Bool) (d : ℕ)
    (hb : b ∈ kurPerms6) (he : e ∈ List.range 3)
    (hpat : kurPatternOK e [t0, t1, t2] = true) (hd : d ∈ List.range 3) :
    kurPhase9 (((kurModelWin b [t0, t1, t2]).drop d).take 9) = d :=
  of_decide_eq_true kurWord_sync_table b hb e he t0 t1 t2 hpat d hd

/-- N11(b): phase recovery for ω. -/
private theorem kurPhase9_window (s : ℕ) :
    kurPhase9 ((List.range 9).map (fun i => kurWord (s + i))) = s % 3 := by
  have hdm := Nat.div_add_mod s 3
  have hsd : s = 3 * (s / 3) + s % 3 := by omega
  have hwin := kurWord_window (s / 3) 3
  have hbits : kurBits (s / 3) 3 =
      [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2)] := rfl
  have hpat : kurPatternOK ((s / 3) % 3)
      [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2)] = true := by
    have h := kurPatternOK_bits (s / 3) 3
    rwa [hbits] at h
  have hmem : kurBlock (s / 3) ∈ kurPerms6 := kurBlock_mem _
  have he : (s / 3) % 3 ∈ List.range 3 := by
    rw [List.mem_range]
    have h3 := Nat.mod_lt (s / 3) (by omega : 0 < 3)
    omega
  have hd : s % 3 ∈ List.range 3 := by
    rw [List.mem_range]
    have h3 := Nat.mod_lt s (by omega : 0 < 3)
    omega
  have htab := kurSyncCheck_apply (kurBlock (s / 3)) ((s / 3) % 3)
    (kurStepBit (s / 3)) (kurStepBit (s / 3 + 1)) (kurStepBit (s / 3 + 2)) (s % 3)
    hmem he hpat hd
  have hlists : (((kurModelWin (kurBlock (s / 3))
      [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2)]).drop
      (s % 3)).take 9) =
      (List.range 9).map (fun i => kurWord (s + i)) := by
    rw [← hbits]
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_take]
    by_cases hn : n < 9
    · rw [ite_eq_left hn, List.getElem?_drop]
      have hMW := hwin.2 (s % 3 + n) (by omega)
      have hR : ((List.range 9).map (fun i => kurWord (s + i)))[n]? =
          some (kurWord (s + n)) := by
        rw [List.getElem?_map, List.getElem?_range hn, Option.map_some]
      rw [hR]
      rwa [show 3 * (s / 3) + (s % 3 + n) = s + n from by omega] at hMW
    · rw [ite_eq_right hn]
      have hR : ((List.range 9).map (fun i => kurWord (s + i)))[n]? = none := by
        rw [List.getElem?_map]
        have hrn : (List.range 9)[n]? = none := by
          apply List.getElem?_eq_none
          have h9 : (List.range 9).length = 9 := by simp
          omega
        rw [hrn, Option.map_none _]
      rw [hR]
  rw [hlists] at htab
  exact htab

/-- N11(c): non-multiple-of-3 periods give m ≤ p + 8. -/
private theorem kurWord_rep_nomod (p s m : ℕ) (hp3 : p % 3 ≠ 0) (h : ORep s m p) :
    m ≤ p + 8 := by
  by_contra hcon
  have hlt : p + 8 < m := by omega
  have hlists : (List.range 9).map (fun i => kurWord (s + i)) =
      (List.range 9).map (fun i => kurWord (s + p + i)) := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < 9
    · have hnp : n + p < m := by omega
      have e := h n hnp
      have ee : s + n + p = s + p + n := by omega
      rw [ee] at e
      have h1 : ((List.range 9).map (fun i => kurWord (s + i)))[n]? =
          some (kurWord (s + n)) := by
        rw [List.getElem?_map, List.getElem?_range hn, Option.map_some]
      have h2 : ((List.range 9).map (fun i => kurWord (s + p + i)))[n]? =
          some (kurWord (s + p + n)) := by
        rw [List.getElem?_map, List.getElem?_range hn, Option.map_some]
      rw [h1, h2, e]
    · have h1 : ((List.range 9).map (fun i => kurWord (s + i)))[n]? = none := by
        rw [List.getElem?_map]
        have hrn : (List.range 9)[n]? = none := by
          apply List.getElem?_eq_none
          have h9 : (List.range 9).length = 9 := by simp
          omega
        rw [hrn, Option.map_none _]
      have h2 : ((List.range 9).map (fun i => kurWord (s + p + i)))[n]? = none := by
        rw [List.getElem?_map]
        have hrn : (List.range 9)[n]? = none := by
          apply List.getElem?_eq_none
          have h9 : (List.range 9).length = 9 := by simp
          omega
        rw [hrn, Option.map_none _]
      rw [h1, h2]
  have e1 := kurPhase9_window s
  have e2 := kurPhase9_window (s + p)
  rw [hlists] at e1
  omega

/-- N12(a): one row of the finite table: some index disagrees. -/
private def kurSmallRow (b : List (Fin 3)) (ts : List Bool) (d p : ℕ) : Bool :=
  List.any (List.range (7 * p / 4 + 1 - p)) (fun i =>
    decide (¬((kurModelWin b ts)[d + i]? = (kurModelWin b ts)[d + i + p]?)))

/-- N12(a): finite table for the seven small periods. -/
private def kurSmallCheck : Bool :=
  List.all kurPerms6 (fun b =>
    List.all (List.range 3) (fun e =>
      List.all [false, true] (fun t0 =>
        List.all [false, true] (fun t1 =>
          List.all [false, true] (fun t2 =>
            List.all [false, true] (fun t3 =>
              List.all [false, true] (fun t4 =>
                List.all [false, true] (fun t5 =>
                  List.all (List.range 3) (fun d =>
                    List.all [1, 2, 4, 5, 7, 8, 10] (fun p =>
                      if kurPatternOK e [t0, t1, t2, t3, t4, t5]
                      then kurSmallRow b [t0, t1, t2, t3, t4, t5] d p
                      else true))))))))))

private theorem kurWord_small_table : kurSmallCheck = true := by decide

private theorem kurSmallCheck_apply (b : List (Fin 3)) (e : ℕ) (t0 t1 t2 t3 t4 t5 : Bool)
    (d p : ℕ) (hb : b ∈ kurPerms6) (he : e < 3)
    (hpat : kurPatternOK e [t0, t1, t2, t3, t4, t5] = true) (hd : d < 3)
    (hmem : p ∈ [1, 2, 4, 5, 7, 8, 10]) :
    kurSmallRow b [t0, t1, t2, t3, t4, t5] d p = true := by
  have h := kurWord_small_table
  simp only [kurSmallCheck, List.all_eq_true] at h
  have h10 := h b hb e (List.mem_range.mpr he) t0 (by cases t0 <;> decide)
    t1 (by cases t1 <;> decide) t2 (by cases t2 <;> decide) t3 (by cases t3 <;> decide)
    t4 (by cases t4 <;> decide) t5 (by cases t5 <;> decide) d (List.mem_range.mpr hd)
    p hmem
  rw [ite_eq_left hpat] at h10
  exact h10

/-- N12(b): the seven small periods satisfy the bound. -/
private theorem kurWord_rep_small_conseq (p s m : ℕ) (hmem : p ∈ [1, 2, 4, 5, 7, 8, 10])
    (h : ORep s m p) : 4 * m ≤ 7 * p := by
  by_contra hcon
  have hlt : 7 * p < 4 * m := by omega
  have hm2 : 7 * p / 4 + 1 ≤ m := by omega
  have hdisj : p = 1 ∨ p = 2 ∨ p = 4 ∨ p = 5 ∨ p = 7 ∨ p = 8 ∨ p = 10 := by
    have hh := hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    exact hh
  have hp10 : p ≤ 10 := by omega
  have hp1 : 1 ≤ p := by omega
  have hdm := Nat.div_add_mod s 3
  have hsd : s = 3 * (s / 3) + s % 3 := by omega
  have hwin := kurWord_window (s / 3) 6
  have hbits : kurBits (s / 3) 6 =
      [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2),
        kurStepBit (s / 3 + 3), kurStepBit (s / 3 + 4), kurStepBit (s / 3 + 5)] :=
    rfl
  have hpat : kurPatternOK ((s / 3) % 3)
      [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2),
        kurStepBit (s / 3 + 3), kurStepBit (s / 3 + 4), kurStepBit (s / 3 + 5)] =
      true := by
    have hh := kurPatternOK_bits (s / 3) 6
    rwa [hbits] at hh
  have hmemB : kurBlock (s / 3) ∈ kurPerms6 := kurBlock_mem _
  have he : (s / 3) % 3 < 3 := Nat.mod_lt _ (by omega)
  have hd : s % 3 < 3 := Nat.mod_lt _ (by omega)
  have htab := kurSmallCheck_apply (kurBlock (s / 3)) ((s / 3) % 3)
    (kurStepBit (s / 3)) (kurStepBit (s / 3 + 1)) (kurStepBit (s / 3 + 2))
    (kurStepBit (s / 3 + 3)) (kurStepBit (s / 3 + 4)) (kurStepBit (s / 3 + 5))
    (s % 3) p hmemB he hpat hd hmem
  have hrow : ∃ i, i ∈ List.range (7 * p / 4 + 1 - p) ∧
      decide (¬((kurModelWin (kurBlock (s / 3))
        [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2),
          kurStepBit (s / 3 + 3), kurStepBit (s / 3 + 4), kurStepBit (s / 3 + 5)])[s % 3 + i]? =
        (kurModelWin (kurBlock (s / 3))
        [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2),
          kurStepBit (s / 3 + 3), kurStepBit (s / 3 + 4), kurStepBit (s / 3 + 5)])[s % 3 + i + p]?))
              =
        true := by
    have hh := htab
    simp only [kurSmallRow, List.any_eq_true] at hh
    exact hh
  obtain ⟨i, hi, hdi⟩ := hrow
  rw [List.mem_range] at hi
  have hne := of_decide_eq_true hdi
  have e1 : (kurModelWin (kurBlock (s / 3))
      [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2),
        kurStepBit (s / 3 + 3), kurStepBit (s / 3 + 4), kurStepBit (s / 3 + 5)])[s % 3 + i]? =
      some (kurWord (s + i)) := by
    rw [← hbits]
    have hMW := hwin.2 (s % 3 + i) (by omega)
    rwa [show 3 * (s / 3) + (s % 3 + i) = s + i from by omega] at hMW
  have e2 : (kurModelWin (kurBlock (s / 3))
      [kurStepBit (s / 3), kurStepBit (s / 3 + 1), kurStepBit (s / 3 + 2),
        kurStepBit (s / 3 + 3), kurStepBit (s / 3 + 4), kurStepBit (s / 3 + 5)])[s % 3 + i + p]? =
      some (kurWord (s + i + p)) := by
    rw [← hbits]
    have hMW := hwin.2 (s % 3 + i + p) (by omega)
    rwa [show 3 * (s / 3) + (s % 3 + i + p) = s + i + p from by omega] at hMW
  have e3 : kurWord (s + i) = kurWord (s + i + p) := h i (by omega)
  rw [e1, e2] at hne
  exact hne (by rw [e3])

/-- N13: every ω-repetition satisfies 4m ≤ 7p. -/
private theorem kurWord_rep_bound (p s m : ℕ) (hp : 1 ≤ p) (h : ORep s m p) :
    4 * m ≤ 7 * p := by
  by_cases hmp : m ≤ p
  · omega
  · have hmp' : p < m := by omega
    by_cases h3 : p % 3 = 0
    · obtain ⟨q, rfl⟩ : ∃ q, p = 3 * q := ⟨p / 3, by omega⟩
      have hq : 1 ≤ q := by omega
      by_cases hm2 : m ≤ 3 * q + 2
      · omega
      · have hm2' : 3 * q + 3 ≤ m := by omega
        obtain ⟨hG, hmM⟩ := kurWord_rep_lift q s m hq hm2' h
        have hN7 := kurGam_rep_bound q (s / 3)
          ((s + (m - 3 * q) - 1) / 3 - s / 3 + 1 + q) hq hG
        omega
    · by_cases h11 : 11 ≤ p
      · have hm8 := kurWord_rep_nomod p s m h3 h
        omega
      · have h11' : p < 11 := by omega
        have hmem : p ∈ [1, 2, 4, 5, 7, 8, 10] := by
          interval_cases p
          · decide
          · decide
          · omega
          · decide
          · decide
          · omega
          · decide
          · decide
          · omega
          · decide
        exact kurWord_rep_small_conseq p s m hmem h

end Kurosaki

/--
**Kurosaki's words are $(7/4)^+$-power-free.** On the alphabet $\{1, 2, 3\}$, let $\sigma$ be the
permutation that swaps $1$ and $2$ and fixes $3$, let $\rho$ be the permutation that swaps $2$ and
$3$ and fixes $1$, and for a finite word $w$ let $\varphi(w) = \sigma(w)\,w\,\rho(w)$, where
$\sigma(w)$ and $\rho(w)$ apply the permutation to each letter of $w$. Call $p \ge 1$ a period of
a finite word $u = u_0 u_1 \cdots$ when $u_i = u_{i+p}$ for every $i$ with $i + p < |u|$. For every
$n \ge 1$, every factor $u$ of the word $\varphi^n(2)$ and every period $p$ of $u$ satisfy
$4|u| \le 7p$; that is, every factor of $\varphi^n(2)$ has exponent at most $7/4$.

Proves `Wanted` entry `kurosaki_phi_pow_power_free`.

Source: Serina Camungol and Narad Rampersad, "Concerning Kurosaki's
Squarefree Word," Journal of Integer Sequences 16 (2013), Article
13.9.4, Theorem (label 7/4powerfree), lines 184–188, with the
σ/ρ/φ definitions at lines 116–124,
https://cs.uwaterloo.ca/journals/JIS/VOL16/Camungol/ramper4.tex
-/
theorem kurosaki_phi_pow_power_free :
    let sigma : Fin 3 → Fin 3 := fun a => if a.val = 0 then 1 else if a.val = 1 then 0 else 2;
    let rho : Fin 3 → Fin 3 := fun a => if a.val = 1 then 2 else if a.val = 2 then 1 else 0;
    let phiW : List (Fin 3) → List (Fin 3) := fun a => (List.map sigma a) ++ a ++ (List.map rho a);
    let W : Nat → List (Fin 3) := fun n => Nat.rec (motive := fun _ => List (Fin 3)) [(1 : Fin 3)]
      (fun _ ih => phiW ih) n;
    ∀ n : Nat, 1 ≤ n → ∀ w l1 l2 : List (Fin 3), W n = l1 ++ w ++ l2 → ∀ p : Nat, 0 < p →
      (∀ i : Nat, i + p < List.length w → w[i]? = w[i + p]?) → 4 * List.length w ≤ 7 * p := by
  intro sigma rho phiW W n hn w l1 l2 h p hp hper
  have hW : ∀ n : ℕ, W n = Kurosaki.kurW n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (List.map sigma (W n) ++ W n) ++ List.map rho (W n) =
        (List.map Kurosaki.kurSigFn (Kurosaki.kurW n) ++ Kurosaki.kurW n) ++
          List.map Kurosaki.kurRhoFn (Kurosaki.kurW n)
      rw [ih]
      rfl
  rw [hW n] at h
  have hsm : l1.length + w.length ≤ 3 ^ n := by
    have hlen : (Kurosaki.kurW n).length = 3 ^ n := Kurosaki.kurW_length n
    rw [h, List.length_append, List.length_append] at hlen
    omega
  have hget : ∀ i : ℕ, i < w.length → w[i]? = (Kurosaki.kurW n)[l1.length + i]? := by
    intro i hi
    have e1 : ((l1 ++ w) ++ l2)[l1.length + i]? = w[i]? := by
      rw [List.getElem?_append_left (by rw [List.length_append]; omega),
        List.getElem?_append_right (by omega),
        show l1.length + i - l1.length = i from by omega]
    rw [← h] at e1
    exact e1.symm
  have hORep : Kurosaki.ORep l1.length w.length p := by
    intro i hi
    have e1 := hget i (by omega)
    have e2 := hget (i + p) (by omega)
    have ee2 : l1.length + (i + p) = l1.length + i + p := by omega
    rw [ee2] at e2
    have ep := hper i (by omega : i + p < w.length)
    have hi1 : l1.length + i < 3 ^ n := by omega
    have hi2 : l1.length + i + p < 3 ^ n := by omega
    have g1 := Kurosaki.kurW_get n (l1.length + i) hi1
    have g2 := Kurosaki.kurW_get n (l1.length + i + p) hi2
    rw [e1, e2, g1, g2] at ep
    have hmul := Option.some_inj.mp ep
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hmul
    have ecancel := (Equiv.apply_eq_iff_eq _).mp hmul
    change Kurosaki.kurGam (l1.length + i) 1 = Kurosaki.kurGam (l1.length + i + p) 1
    exact ecancel
  exact Kurosaki.kurWord_rep_bound p l1.length w.length hp hORep

end MetaMathlibExt
end
