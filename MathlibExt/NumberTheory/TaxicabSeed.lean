/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

private lemma card_le_sum_of_one_le (M : Multiset ℕ) (h : ∀ x ∈ M, 1 ≤ x) :
    M.card ≤ M.sum := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.sum_cons]
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have ih' := ih hs
    omega

private lemma repSet_finite (n v m : ℕ) (hm : 1 ≤ m) : {M : Multiset ℕ |
    M.card = n ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v}.Finite := by
  classical
  have hm0 : m ≠ 0 := by omega
  apply Set.Finite.subset (Finset.finite_toSet
    ((((Finset.range (v + 1)).val.bind (fun x => Multiset.replicate n x)).powersetCard n).toFinset))
  intro M hM
  rw [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powersetCard]
  obtain ⟨hcard, hpos, hsum⟩ := hM
  refine ⟨?_, hcard⟩
  rw [Multiset.le_iff_count]
  intro a
  by_cases ha : a ≤ v
  · calc Multiset.count a M ≤ M.card := Multiset.count_le_card a M
      _ = n := hcard
      _ = Multiset.count a ((Finset.range (v + 1)).val.bind
          (fun x => Multiset.replicate n x)) := by
        have hcount : Multiset.count a ((Finset.range (v + 1)).val.bind
            (fun x => Multiset.replicate n x)) = n := by
          rw [Multiset.count_bind]
          have hrfl : (Multiset.map (fun y => Multiset.count a (Multiset.replicate n y))
              (Finset.range (v + 1)).val).sum
              = Finset.sum (Finset.range (v + 1))
                (fun y => Multiset.count a (Multiset.replicate n y)) := rfl
          rw [hrfl]
          simp only [Multiset.count_replicate]
          rw [Finset.sum_ite_eq']
          have hmem : a ∈ Finset.range (v + 1) := Finset.mem_range.mpr (by omega)
          simp [hmem]
        exact hcount.symm
  · have hlt : v < a := not_le.mp ha
    have hni : a ∉ M := by
      intro ham
      have h1 : a ≤ a ^ m := Nat.le_self_pow hm0 a
      have hmem : a ^ m ∈ M.map (fun x => x ^ m) := Multiset.mem_map_of_mem _ ham
      have hle : a ^ m ≤ (M.map (fun x => x ^ m)).sum :=
        Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
      rw [hsum] at hle
      omega
    rw [Multiset.count_eq_zero.mpr hni]
    exact Nat.zero_le _

private lemma pad_ncard_le (n v m : ℕ) (hm : 1 ≤ m) :
    {M : Multiset ℕ | M.card = n ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v}.ncard ≤
    {M : Multiset ℕ | M.card = n + 1 ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v + 1}.ncard := by
  classical
  have hinj : Function.Injective (fun M : Multiset ℕ => 1 ::ₘ M) := by
    intro M₁ M₂ h
    exact (Multiset.cons_inj_right 1).mp h
  have hmaps : ∀ M ∈ {M : Multiset ℕ | M.card = n ∧ (∀ x ∈ M, 0 < x) ∧
      (M.map (fun x => x ^ m)).sum = v},
      (1 ::ₘ M) ∈ {M : Multiset ℕ | M.card = n + 1 ∧ (∀ x ∈ M, 0 < x) ∧
        (M.map (fun x => x ^ m)).sum = v + 1} := by
    intro M hM
    obtain ⟨hc, hp, hs⟩ := hM
    refine ⟨by rw [Multiset.card_cons, hc], ?_, ?_⟩
    · intro x hx
      rw [Multiset.mem_cons] at hx
      rcases hx with rfl | hx
      · exact zero_lt_one
      · exact hp x hx
    · rw [Multiset.map_cons, Multiset.sum_cons, one_pow, hs, Nat.add_comm]
  calc {M : Multiset ℕ | M.card = n ∧ (∀ x ∈ M, 0 < x) ∧
        (M.map (fun x => x ^ m)).sum = v}.ncard
      = ((fun M : Multiset ℕ => 1 ::ₘ M) '' {M : Multiset ℕ | M.card = n ∧
        (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v}).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ {M : Multiset ℕ | M.card = n + 1 ∧ (∀ x ∈ M, 0 < x) ∧
        (M.map (fun x => x ^ m)).sum = v + 1}.ncard := by
        apply Set.ncard_le_ncard _ (repSet_finite _ _ _ hm)
        rw [Set.image_subset_iff]
        intro M hM
        exact hmaps M hM

private lemma rep_ge_card (n v m t : ℕ) (ht : 1 ≤ t)
    (h : t ≤ {M : Multiset ℕ | M.card = n ∧ (∀ x ∈ M, 0 < x) ∧
      (M.map (fun x => x ^ m)).sum = v}.ncard)
    (hm : 1 ≤ m) : n ≤ v := by
  classical
  have hfin := repSet_finite n v m hm
  have hpos : 0 < {M : Multiset ℕ | M.card = n ∧ (∀ x ∈ M, 0 < x) ∧
      (M.map (fun x => x ^ m)).sum = v}.ncard := by omega
  rw [Set.ncard_pos hfin] at hpos
  obtain ⟨M, hM⟩ := hpos
  obtain ⟨hc, hp, hs⟩ := hM
  have h1 : ∀ y ∈ M.map (fun x => x ^ m), 1 ≤ y := by
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Nat.one_le_pow m x (hp x hx)
  have h2 := card_le_sum_of_one_le _ h1
  rw [Multiset.card_map, hc, hs] at h2
  exact h2

private lemma collision_exists (m t : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    ∃ v, t ≤ {M : Multiset ℕ | M.card = m + 1 ∧ (∀ x ∈ M, 0 < x) ∧
      (M.map (fun x => x ^ m)).sum = v}.ncard := by
  classical
  set W : ℕ := (m + 1) ^ m * (((m + 1) + 1) * (t - 1)) + 1 with hW
  set X : ℕ := (m + 1) * W with hX
  set e : Fin (m + 1) → Fin W → ℕ := fun j i => j.val * W + i.val + 1 with he
  set φ : Finset ℕ → ℕ := fun s => ∑ x ∈ s, x ^ m with hφ
  set P : Finset (Finset ℕ) := Finset.image
    (fun g : Fin (m + 1) → Fin W =>
      Finset.image (fun j => e j (g j)) Finset.univ) Finset.univ with hP
  have hWpos : 0 < W := by omega
  have ediv : ∀ (j : Fin (m + 1)) (i : Fin W),
      (j.val * W + i.val) / W = j.val := by
    intro j i
    have hform : j.val * W + i.val = i.val + j.val * W := by ring
    rw [hform, Nat.add_mul_div_right _ _ hWpos, Nat.div_eq_of_lt i.isLt,
      Nat.zero_add]
  have emod : ∀ (j : Fin (m + 1)) (i : Fin W),
      (j.val * W + i.val) % W = i.val := by
    intro j i
    have hform : j.val * W + i.val = i.val + j.val * W := by ring
    rw [hform, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  have hsg_inj : ∀ g : Fin (m + 1) → Fin W,
      Function.Injective (fun j => e j (g j)) := by
    intro g j₁ j₂ h
    simp only [he] at h
    have hcancel := Nat.add_right_cancel h
    have c1 := congrArg (fun x => x / W) hcancel
    rw [ediv, ediv] at c1
    exact Fin.ext_iff.mpr c1
  have hP_inj : Function.Injective (fun g : Fin (m + 1) → Fin W =>
      Finset.image (fun j => e j (g j)) Finset.univ) := by
    intro g₁ g₂ h
    have h2 : Finset.image (fun j' => e j' (g₁ j')) Finset.univ =
        Finset.image (fun j' => e j' (g₂ j')) Finset.univ := h
    funext j
    rw [Fin.ext_iff]
    have hmem : e j (g₁ j) ∈
        Finset.image (fun j' => e j' (g₂ j')) Finset.univ := by
      rw [← h2]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hmem
    simp only [he] at hj'
    have hcancel := Nat.add_right_cancel hj'
    have c1 := congrArg (fun x => x / W) hcancel
    rw [ediv, ediv] at c1
    have hjj : j = j' := Fin.ext_iff.mpr c1.symm
    subst hjj
    have c2 := congrArg (fun x => x % W) hcancel
    rw [emod, emod] at c2
    exact c2.symm
  have hsg_card : ∀ g : Fin (m + 1) → Fin W,
      (Finset.image (fun j => e j (g j)) Finset.univ).card = m + 1 := by
    intro g
    rw [Finset.card_image_of_injective Finset.univ (hsg_inj g),
      Finset.card_univ, Fintype.card_fin]
  have hPcard : P.card = W ^ (m + 1) := by
    rw [hP, Finset.card_image_of_injective Finset.univ hP_inj,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have ebound : ∀ (j : Fin (m + 1)) (i : Fin W),
      j.val * W + i.val + 1 ≤ (m + 1) * W := by
    intro j i
    have hj : j.val * W ≤ m * W := by
      have h : j.val ≤ m := by
        have h := j.isLt
        omega
      exact Nat.mul_le_mul h le_rfl
    have hi : i.val + 1 ≤ W := by
      have h := i.isLt
      omega
    have h2 : (m + 1) * W = m * W + W := by ring
    omega
  have hphi_le : ∀ g : Fin (m + 1) → Fin W,
      φ (Finset.image (fun j => e j (g j)) Finset.univ) ≤ (m + 1) * X ^ m := by
    intro g
    simp only [hφ]
    calc ∑ x ∈ Finset.image (fun j => e j (g j)) Finset.univ, x ^ m
        ≤ (Finset.image (fun j => e j (g j)) Finset.univ).card • X ^ m := by
          apply Finset.sum_le_card_nsmul
          intro x hx
          obtain ⟨j, _, hjx⟩ := Finset.mem_image.mp hx
          apply Nat.pow_le_pow_left _ m
          simp only [he] at hjx
          have hb := ebound j (g j)
          omega
      _ = (m + 1) * X ^ m := by
          rw [hsg_card g, nsmul_eq_mul, Nat.cast_id]
  have hmaps : Set.MapsTo φ ↑P ↑(Finset.range ((m + 1) * X ^ m + 1)) := by
    intro s hs
    rw [hP, Finset.mem_coe] at hs
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hs
    rw [Finset.mem_coe, Finset.mem_range]
    exact lt_of_le_of_lt (hphi_le g) (Nat.lt_succ_self _)
  have hX1 : 1 ≤ X := by
    rw [hX]
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ (m + 1) * W := Nat.mul_le_mul (by omega) (by omega)
  have hXm : 1 ≤ X ^ m := Nat.one_le_pow m X hX1
  have hB : (m + 1) ^ m * (((m + 1) + 1) * (t - 1)) < W := by omega
  have hWm : 0 < W ^ m := pow_pos hWpos m
  have hnum : ((m + 1) * X ^ m + 1) * (t - 1) < W ^ (m + 1) := by
    calc ((m + 1) * X ^ m + 1) * (t - 1)
        ≤ ((m + 1) * X ^ m + X ^ m) * (t - 1) := by
          have hle : (m + 1) * X ^ m + 1 ≤ (m + 1) * X ^ m + X ^ m := by
            omega
          exact Nat.mul_le_mul hle le_rfl
      _ = X ^ m * (((m + 1) + 1) * (t - 1)) := by ring
      _ = ((m + 1) * W) ^ m * (((m + 1) + 1) * (t - 1)) := by rw [hX]
      _ = W ^ m * ((m + 1) ^ m * (((m + 1) + 1) * (t - 1))) := by
          rw [mul_pow]; ring
      _ < W ^ m * W := mul_lt_mul_of_pos_left hB hWm
      _ = W ^ (m + 1) := (pow_succ W m).symm
  obtain ⟨y, _, hyt⟩ :
      ∃ y ∈ Finset.range ((m + 1) * X ^ m + 1),
        t ≤ (P.filter (fun s => φ s = y)).card := by
    by_contra hcon
    rw [not_exists] at hcon
    have hall : ∀ y ∈ Finset.range ((m + 1) * X ^ m + 1),
        (P.filter (fun s => φ s = y)).card < t := by
      intro y hy
      have hle : t ≤ (P.filter (fun s => φ s = y)).card → False := by
        intro hle
        exact hcon y ⟨hy, hle⟩
      by_contra hlt
      exact hle (not_lt.mp hlt)
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    have hle2 : ∑ y ∈ Finset.range ((m + 1) * X ^ m + 1),
        (P.filter (fun s => φ s = y)).card ≤
        (Finset.range ((m + 1) * X ^ m + 1)).card • (t - 1) := by
      apply Finset.sum_le_card_nsmul
      intro y hy
      have h := hall y hy
      omega
    rw [Finset.card_range, nsmul_eq_mul, Nat.cast_id] at hle2
    rw [hPcard] at hsum
    omega
  obtain ⟨F', hF'sub, hF'card⟩ := Finset.exists_subset_card_eq hyt
  have hvalinj : Function.Injective (fun s : Finset ℕ => s.val) :=
    Finset.val_injective
  have hGcard : ((fun s : Finset ℕ => s.val) '' ↑F').ncard = t := by
    rw [Set.ncard_image_of_injective _ hvalinj,
      Set.ncard_coe_finset, hF'card]
  have hGsub : ((fun s : Finset ℕ => s.val) '' ↑F') ⊆
      {M : Multiset ℕ | M.card = m + 1 ∧
      (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = y} := by
    intro M hM
    obtain ⟨s, hs, rfl⟩ := hM
    rw [Finset.mem_coe] at hs
    have hsF : s ∈ P.filter (fun s => φ s = y) := hF'sub hs
    rw [Finset.mem_filter] at hsF
    obtain ⟨hsP, hsy⟩ := hsF
    rw [hP] at hsP
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hsP
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.card_val]
      exact hsg_card g
    · intro x hx
      rw [Finset.mem_val] at hx
      obtain ⟨j, _, hjx⟩ := Finset.mem_image.mp hx
      simp only [he] at hjx
      omega
    · exact hsy
  have hle := Set.ncard_le_ncard hGsub (repSet_finite (m + 1) y m hm)
  rw [hGcard] at hle
  exact ⟨y, hle⟩

/-! # Generalized taxicab seed numbers
-/

/--
**Existence of seeds for generalized taxicab numbers.** Fix natural numbers $m \ge 1$ and
$t \ge 1$, and let $T(n, m, t)$ be, for each natural number $n$, either a natural number or
undefined, such that for all natural numbers $n$ and $v$, $T(n, m, t)$ is defined and equals $v$
exactly when $v$ is the least natural number with at least $t$ representations as a sum of exactly
$n$ positive $m$-th powers, representations being counted as unordered multisets of summands.
Then there is a positive integer $s_0$ such that $T(s_0, m, t)$ is defined, say equal to $v_0$,
and $T(s_0 + k, m, t) = v_0 + k$ for every natural number $k$; moreover, $s_0$ is the least
positive integer $s$ for which $T(s, m, t)$ is defined and $T(s + k, m, t) = T(s, m, t) + k$ for
every natural number $k$.

Source: Jeffrey H. Dinitz, Richard A. Games, and Robert L. Roth, “Seeds for Generalized Taxicab Numbers”, Journal of Integer Sequences 22 (2019), Article 19.3.3, Theorem line 229, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Dinitz/dinitz8.tex>.
Proves `Wanted` entry `generalized_taxicab_seed_exists`.
-/
theorem generalized_taxicab_seed_exists
    (m t : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t)
    (T : ℕ → ℕ → ℕ → Option ℕ)
    (hT : ∀ n v : ℕ, T n m t = some v ↔
      (t ≤ Set.ncard {M : Multiset ℕ |
          M.card = n ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v} ∧
        ∀ v' : ℕ, v' < v →
          ¬ (t ≤ Set.ncard {M : Multiset ℕ |
            M.card = n ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v'}))) :
    ∃ s₀ : ℕ, 0 < s₀ ∧
      (∃ v₀ : ℕ, T s₀ m t = some v₀ ∧ ∀ k : ℕ, T (s₀ + k) m t = some (v₀ + k)) ∧
      ∀ s : ℕ, 0 < s →
        (∃ v : ℕ, T s m t = some v ∧ ∀ k : ℕ, T (s + k) m t = some (v + k)) →
        s₀ ≤ s := by
  classical
  set V : ℕ → Set ℕ := fun n => {v | t ≤ Set.ncard {M : Multiset ℕ |
      M.card = n ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v}} with hV
  have hprop : ∀ n, (V n).Nonempty → (V (n + 1)).Nonempty := by
    intro n hne
    obtain ⟨v, hv⟩ := hne
    exact ⟨v + 1, le_trans hv (pad_ncard_le n v m hm)⟩
  obtain ⟨vB, hvB⟩ := collision_exists m t hm ht
  have hEx : ∀ n, m + 1 ≤ n → (V n).Nonempty := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => simpa using ⟨vB, hvB⟩
    | succ k ih => exact hprop _ (ih (by omega))
  have hamem : ∀ n, m + 1 ≤ n → sInf (V n) ∈ V n := fun n hn =>
    Nat.sInf_mem (hEx n hn)
  have haT : ∀ n, m + 1 ≤ n → T n m t = some (sInf (V n)) := by
    intro n hn
    refine (hT n _).mpr ⟨hamem n hn, ?_⟩
    intro v' hv' hcon
    have hcon' : v' ∈ V n := hcon
    exact absurd (Nat.sInf_le hcon') (by omega)
  have ha_ge : ∀ n, m + 1 ≤ n → n ≤ sInf (V n) := by
    intro n hn
    apply le_csInf (hEx n hn)
    intro v hv
    exact rep_ge_card n v m t ht hv hm
  have ha_step : ∀ n, m + 1 ≤ n → sInf (V (n + 1)) ≤ sInf (V n) + 1 := by
    intro n hn
    apply Nat.sInf_le
    show t ≤ Set.ncard {M : Multiset ℕ | M.card = n + 1 ∧ (∀ x ∈ M, 0 < x) ∧
      (M.map (fun x => x ^ m)).sum = sInf (V n) + 1}
    exact le_trans (hamem n hn) (pad_ncard_le n (sInf (V n)) m hm)
  have hb_step : ∀ j, sInf (V (m + 1 + (j + 1))) - (m + 1 + (j + 1)) ≤
      sInf (V (m + 1 + j)) - (m + 1 + j) := by
    intro j
    have e1 : m + 1 + (j + 1) = (m + 1 + j) + 1 := by omega
    rw [e1]
    have h := ha_step (m + 1 + j) (by omega)
    omega
  have hb_anti : ∀ j k, sInf (V (m + 1 + (j + k))) - (m + 1 + (j + k)) ≤
      sInf (V (m + 1 + j)) - (m + 1 + j) := by
    intro j k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have e : j + (k + 1) = (j + k) + 1 := by omega
      rw [e]
      exact le_trans (hb_step (j + k)) ih
  have hbrange : (Set.range fun j => sInf (V (m + 1 + j)) - (m + 1 + j)).Nonempty :=
    ⟨_, ⟨0, rfl⟩⟩
  obtain ⟨j₀, hj₀⟩ := Nat.sInf_mem hbrange
  have hL_le : ∀ j, sInf (Set.range fun j => sInf (V (m + 1 + j)) - (m + 1 + j)) ≤
      sInf (V (m + 1 + j)) - (m + 1 + j) := fun j =>
    Nat.sInf_le ⟨j, rfl⟩
  have hj₀b : sInf (V (m + 1 + j₀)) - (m + 1 + j₀) =
      sInf (Set.range fun j => sInf (V (m + 1 + j)) - (m + 1 + j)) := hj₀
  have hb_const : ∀ k, sInf (V (m + 1 + (j₀ + k))) - (m + 1 + (j₀ + k)) =
      sInf (Set.range fun j => sInf (V (m + 1 + j)) - (m + 1 + j)) := by
    intro k
    apply le_antisymm _ (hL_le (j₀ + k))
    calc sInf (V (m + 1 + (j₀ + k))) - (m + 1 + (j₀ + k))
        ≤ sInf (V (m + 1 + j₀)) - (m + 1 + j₀) := hb_anti j₀ k
      _ = sInf (Set.range fun j => sInf (V (m + 1 + j)) - (m + 1 + j)) := hj₀b
  have hval : ∀ k, sInf (V (m + 1 + (j₀ + k))) = sInf (V (m + 1 + j₀)) + k := by
    intro k
    have h0 : m + 1 + j₀ ≤ sInf (V (m + 1 + j₀)) := ha_ge _ (by omega)
    have h1 : m + 1 + (j₀ + k) ≤ sInf (V (m + 1 + (j₀ + k))) := ha_ge _ (by omega)
    have nk : m + 1 + (j₀ + k) = (m + 1 + j₀) + k := by omega
    have e0 : sInf (V (m + 1 + j₀)) =
        sInf (Set.range fun j => sInf (V (m + 1 + j)) - (m + 1 + j)) + (m + 1 + j₀) := by
      omega
    have hk := hb_const k
    have ek : sInf (V (m + 1 + (j₀ + k))) =
        sInf (Set.range fun j => sInf (V (m + 1 + j)) - (m + 1 + j)) + (m + 1 + (j₀ + k)) := by
      omega
    omega
  have hseed_T : ∀ k, T (m + 1 + j₀ + k) m t =
      some (sInf (V (m + 1 + j₀)) + k) := by
    intro k
    have e : m + 1 + j₀ + k = m + 1 + (j₀ + k) := by omega
    rw [e, ← hval k]
    exact haT _ (by omega)
  have hSeed : 0 < m + 1 + j₀ ∧ ∃ v, T (m + 1 + j₀) m t = some v ∧
      ∀ k, T (m + 1 + j₀ + k) m t = some (v + k) := by
    refine ⟨by omega, sInf (V (m + 1 + j₀)), hseed_T 0, ?_⟩
    simpa using hseed_T
  set Seeds : Set ℕ := {s | 0 < s ∧ ∃ v, T s m t = some v ∧
    ∀ k, T (s + k) m t = some (v + k)} with hSeeds
  have hSeeds_ne : Seeds.Nonempty := ⟨_, hSeed⟩
  obtain ⟨hpos, v₀, hv₀, hvall⟩ := Nat.sInf_mem hSeeds_ne
  refine ⟨sInf Seeds, hpos, ⟨v₀, hv₀, hvall⟩, ?_⟩
  intro s hs hmem
  exact Nat.sInf_le ⟨hs, hmem⟩

end MetaMathlibExt
