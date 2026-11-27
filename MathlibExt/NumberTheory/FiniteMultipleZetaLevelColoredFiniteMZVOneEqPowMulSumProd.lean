/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Decomposition of finite multiple zeta values into level pieces

Colored finite multiple harmonic sums and their decomposition into consecutive level pieces.

Source: Shin-ichiro Seki, *Regular Primes, Non-Wieferich Primes, and Finite
Multiple Zeta Values of Level N*, INTEGERS 24 (2024), Article A22 (arXiv:2310.06809).
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

open scoped Classical in
/-- **Colored finite multiple harmonic sums.** Let $p$ and $N$ be natural numbers, let
$k = (k_1, \dots, k_r)$ be a finite sequence of natural numbers and let
$\alpha = (\alpha_1, \dots, \alpha_r) \in (\mathbb{Z}/N\mathbb{Z})^r$. The colored finite multiple
harmonic sum $\zeta^{\alpha}_{p,N}(k) \in \mathbb{Z}/p\mathbb{Z}$ is the sum of
$m_1^{-k_1} \cdots m_r^{-k_r}$ over all integers $0 < m_1 < \dots < m_r < p$ with
$m_i \equiv \alpha_i \pmod N$ for every $i$.

Here $m^{-1}$ is the inverse of $m$ in $\mathbb{Z}/p\mathbb{Z}$; when $p$ is prime every
$0 < m < p$ is invertible, and for other $p$ non-units get a conventional value.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Section 2.2 (definition of `ζ^α_{p,N}(k)`). -/
noncomputable def coloredFiniteMZV (p N : ℕ) {r : ℕ} (k : Fin r → ℕ) (α : Fin r → ZMod N) :
    ZMod p :=
  ∑ m ∈ (Finset.univ : Finset (Fin r → Fin p)).filter
      (fun m : Fin r → Fin p => StrictMono m ∧
        ∀ i, 0 < (m i : ℕ) ∧ ((m i : ℕ) : ZMod N) = α i),
    ∏ i, (((m i : ℕ) : ZMod p)⁻¹) ^ k i

private def cutVal (N r : ℕ) (i : Fin (N - 1) → Fin (r + 1)) (t : ℕ) : ℕ :=
  if t = 0 then 0 else if h : t - 1 < N - 1 then (i ⟨t - 1, h⟩ : ℕ) else r

private lemma cutVal_zero (N r : ℕ) (i : Fin (N - 1) → Fin (r + 1)) :
    cutVal N r i 0 = 0 := by simp [cutVal]

private lemma cutVal_le (N r : ℕ) (i : Fin (N - 1) → Fin (r + 1)) (t : ℕ) :
    cutVal N r i t ≤ r := by
  unfold cutVal
  split
  · omega
  · split
    · exact Nat.le_of_lt_succ (i _).isLt
    · rfl

private lemma cutVal_N (N r : ℕ) (hN : 0 < N) (i : Fin (N - 1) → Fin (r + 1)) :
    cutVal N r i N = r := by simp [cutVal, Nat.ne_of_gt hN]

private lemma cutVal_mono (N r : ℕ) (i : Fin (N - 1) → Fin (r + 1))
    (hi : Monotone i) : Monotone (cutVal N r i) := by
  intro a b hab
  unfold cutVal
  split
  · exact Nat.zero_le _
  · split
    · split
      · omega
      · split
        · exact hi (by simp only [Fin.le_iff_val_le_val]; omega)
        · exact Nat.le_of_lt_succ (i _).isLt
    · split
      · omega
      · split
        · omega
        · rfl

private def blockId (N p : ℕ) (hN : 0 < N) (v : Fin p) : Fin N :=
  ⟨N * v.val / p, by
    have hp : 0 < p := Nat.zero_lt_of_lt v.isLt
    apply (Nat.div_lt_iff_lt_mul hp).2
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left v.isLt hN⟩

private lemma blockId_lo (N p : ℕ) (hN : 0 < N) (v : Fin p) :
    (blockId N p hN v : ℕ) * p ≤ N * (v : ℕ) :=
  Nat.div_mul_le_self _ _

private lemma blockId_hi (N p : ℕ) (hN : 0 < N) (v : Fin p) :
    N * (v : ℕ) < ((blockId N p hN v : ℕ) + 1) * p := by
  have hp : 0 < p := Nat.zero_lt_of_lt v.isLt
  exact (Nat.div_lt_iff_lt_mul hp).1 (Nat.lt_succ_self _)

private lemma blockId_strict (N p : ℕ) (hN : 0 < N) (hpN : N < p) (hp : p.Prime)
    (v : Fin p) (hv : 0 < (v : ℕ)) :
    (blockId N p hN v : ℕ) * p < N * (v : ℕ) := by
  apply lt_of_le_of_ne (blockId_lo N p hN v)
  intro h
  have hd : p ∣ N * (v : ℕ) := ⟨blockId N p hN v, by simpa [Nat.mul_comm] using h.symm⟩
  rcases hp.dvd_mul.mp hd with h | h
  · exact (Nat.not_dvd_of_pos_of_lt hN hpN) h
  · exact (Nat.not_dvd_of_pos_of_lt hv v.isLt) h

private lemma blockId_mono (N p : ℕ) (hN : 0 < N) : Monotone (blockId N p hN) := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.mul_le_mul_left N hab)

private lemma interval_order (N p j k a b : ℕ) (hjk : j < k)
    (ha : N * a < (j + 1) * p) (hb : k * p < N * b) : a < b := by
  have h := Nat.mul_le_mul_right p (show j + 1 ≤ k by omega)
  have hab : N * a < N * b := lt_trans (lt_of_lt_of_le ha h) hb
  exact Nat.lt_of_mul_lt_mul_left hab

open scoped Classical in
private def cuts (N r : ℕ) (b : Fin r → Fin N) : Fin (N - 1) → Fin (r + 1) :=
  fun t : Fin (N - 1) => ⟨(Finset.univ.filter fun u : Fin r => (b u : ℕ) < t.val + 1).card,
    Nat.lt_succ_of_le (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (s := (Finset.univ : Finset (Fin r))) _))⟩

private lemma cuts_mono (N r : ℕ) (b : Fin r → Fin N) : Monotone (cuts N r b) := by
  classical
  intro a c hac
  change (Finset.univ.filter fun u : Fin r => (b u : ℕ) < a.val + 1).card ≤
    (Finset.univ.filter fun u : Fin r => (b u : ℕ) < c.val + 1).card
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact lt_of_lt_of_le hu (Nat.add_le_add_right hac 1)

private lemma cutVal_count (N r : ℕ) (b : Fin r → Fin N) (t : ℕ) :
    cutVal N r (cuts N r b) t =
      (Finset.univ.filter fun u : Fin r => (b u : ℕ) < t).card := by
  classical
  by_cases ht : t = 0
  · subst t; simp [cutVal]
  by_cases h : t - 1 < N - 1
  · simp [cutVal, ht, h, cuts, Nat.sub_add_cancel (by omega : 1 ≤ t)]
  · have hall : ∀ u : Fin r, (b u : ℕ) < t := fun u => by have := (b u).isLt; omega
    simp [cutVal, ht, h, hall]

private lemma cutVal_iff (N r : ℕ) (b : Fin r → Fin N) (hb : Monotone b)
    (u : Fin r) (t : ℕ) :
    (u : ℕ) < cutVal N r (cuts N r b) t ↔ (b u : ℕ) < t := by
  classical
  rw [cutVal_count]
  exact Tuple.lt_card_lt_iff_apply_lt_of_monotone
    (show Monotone (fun u => (b u : ℕ)) from fun _ _ h => hb h)

private abbrev slice (κ : List ℕ) (N : ℕ) (i : Fin (N - 1) → Fin (κ.length + 1))
    (j : Fin N) : List ℕ :=
  (κ.drop (cutVal N κ.length i j)).take
    (cutVal N κ.length i ((j : ℕ) + 1) - cutVal N κ.length i j)

private lemma slice_length (κ : List ℕ) (N : ℕ)
    (i : Fin (N - 1) → Fin (κ.length + 1)) (j : Fin N) :
    (slice κ N i j).length =
      cutVal N κ.length i ((j : ℕ) + 1) - cutVal N κ.length i j := by
  simp only [slice, List.length_take, List.length_drop]
  exact Nat.min_eq_left (Nat.sub_le_sub_right (cutVal_le N κ.length i _) _)
private lemma block_exists (N r : ℕ) (hN : 0 < N) (e : ℕ → ℕ) (he0 : e 0 = 0)
    (heN : e N = r) (u : Fin r) :
    ∃ j : Fin N, e j ≤ u.val ∧ u.val < e (j.val + 1) := by
  have hex : ∃ t : ℕ, u.val < e (t + 1) :=
    ⟨N - 1, by simpa only [Nat.sub_add_cancel hN, heN] using u.isLt⟩
  let j := Nat.find hex
  have hj : j < N := by have := Nat.find_min' hex (show u.val < e (N - 1 + 1) by
    simpa only [Nat.sub_add_cancel hN, heN] using u.isLt); dsimp [j]; omega
  refine ⟨⟨j, hj⟩, ?_, Nat.find_spec hex⟩
  by_cases h : j = 0
  · simp [h, he0]
  · have hh := Nat.find_min hex (show j - 1 < Nat.find hex by dsimp [j]; omega)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using Nat.le_of_not_gt hh

private def partPos (N r : ℕ) (i : Fin (N - 1) → Fin (r + 1)) (hi : Monotone i)
    (z : (j : Fin N) × Fin (cutVal N r i (j.val + 1) - cutVal N r i j)) : Fin r :=
  ⟨cutVal N r i z.1 + z.2.val, by
    have ht := z.2.isLt
    have hm := cutVal_mono N r i hi (Nat.le_succ z.1.val)
    have hr := cutVal_le N r i (z.1.val + 1)
    omega⟩

private lemma partPos_lt_iff (N r : ℕ) (i : Fin (N - 1) → Fin (r + 1))
    (hi : Monotone i)
    (z : (j : Fin N) × Fin (cutVal N r i (j.val + 1) - cutVal N r i j)) (t : ℕ) :
    (partPos N r i hi z : ℕ) < cutVal N r i t ↔ z.1.val < t := by
  have hz := z.2.isLt
  have hm := cutVal_mono N r i hi (Nat.le_succ z.1.val)
  change cutVal N r i z.1 + z.2.val < cutVal N r i t ↔ z.1.val < t
  constructor
  · intro h
    by_contra hn
    have hh := cutVal_mono N r i hi (show t ≤ z.1.val by omega)
    omega
  · intro h
    have hh := cutVal_mono N r i hi (show z.1.val + 1 ≤ t by omega)
    omega

private lemma partPos_bijective (N r : ℕ) (hN : 0 < N)
    (i : Fin (N - 1) → Fin (r + 1)) (hi : Monotone i) :
    Function.Bijective (partPos N r i hi) := by
  constructor
  · intro a b hab
    have hv := congrArg Fin.val hab
    have hj : a.1 = b.1 := by
      apply Fin.ext
      have ha := partPos_lt_iff N r i hi a (b.1.val + 1)
      have hb := partPos_lt_iff N r i hi b (a.1.val + 1)
      have haa := partPos_lt_iff N r i hi a (a.1.val + 1)
      have hbb := partPos_lt_iff N r i hi b (b.1.val + 1)
      omega
    obtain ⟨a, ta⟩ := a
    obtain ⟨b, tb⟩ := b
    dsimp at hj
    subst b
    congr 1
    apply Fin.ext
    change cutVal N r i a + ta.val = cutVal N r i a + tb.val at hv
    omega
  · intro u
    obtain ⟨j, hjlo, hjhi⟩ := block_exists N r hN (cutVal N r i)
      (cutVal_zero N r i) (cutVal_N N r hN i) u
    refine ⟨⟨j, ⟨u.val - cutVal N r i j, by omega⟩⟩, ?_⟩
    apply Fin.ext
    change cutVal N r i j + (u.val - cutVal N r i j) = u.val
    omega

private noncomputable def partEquiv (N r : ℕ) (hN : 0 < N)
    (i : Fin (N - 1) → Fin (r + 1)) (hi : Monotone i) :
    ((j : Fin N) × Fin (cutVal N r i (j.val + 1) - cutVal N r i j)) ≃ Fin r :=
  Equiv.ofBijective (partPos N r i hi) (partPos_bijective N r hN i hi)

private abbrev Global (p r : ℕ) :=
  {m : Fin r → Fin p // StrictMono m ∧ ∀ u, 0 < (m u : ℕ)}

private abbrev Block (N p j s : ℕ) :=
  {m : Fin s → Fin p // StrictMono m ∧
    ∀ u, j * p < N * (m u : ℕ) ∧ N * (m u : ℕ) < (j + 1) * p}

private abbrev Cut (N r : ℕ) := {i : Fin (N - 1) → Fin (r + 1) // Monotone i}

open scoped Classical in
private noncomputable def globalCut (N p r : ℕ) (hN : 0 < N) (m : Global p r) : Cut N r :=
  ⟨cuts N r (blockId N p hN ∘ m.val), cuts_mono N r _⟩

private lemma globalCut_block (N p r : ℕ) (hN : 0 < N) (m : Global p r)
    (z : (j : Fin N) × Fin
      (cutVal N r (globalCut N p r hN m).val (j.val + 1) -
        cutVal N r (globalCut N p r hN m).val j)) :
    blockId N p hN (m.val (partPos N r (globalCut N p r hN m).val
      (globalCut N p r hN m).property z)) = z.1 := by
  have hb : Monotone (blockId N p hN ∘ m.val) :=
    (blockId_mono N p hN).comp m.property.1.monotone
  have h1 := cutVal_iff N r _ hb
    (partPos N r (globalCut N p r hN m).val (globalCut N p r hN m).property z) z.1.val
  have h2 := cutVal_iff N r _ hb
    (partPos N r (globalCut N p r hN m).val (globalCut N p r hN m).property z)
    (z.1.val + 1)
  have hp1 := partPos_lt_iff N r (globalCut N p r hN m).val
    (globalCut N p r hN m).property z z.1.val
  have hp2 := partPos_lt_iff N r (globalCut N p r hN m).val
    (globalCut N p r hN m).property z (z.1.val + 1)
  apply Fin.ext
  change (_ < cutVal N r (globalCut N p r hN m).val z.1.val ↔ _) at h1
  change (_ < cutVal N r (globalCut N p r hN m).val (z.1.val + 1) ↔ _) at h2
  simp only [Function.comp_apply] at h1 h2
  omega

private noncomputable def restrictGlobal (N p r : ℕ) (hN : 0 < N) (hpN : N < p)
    (hp : p.Prime) (m : Global p r) (j : Fin N) :
    Block N p j (cutVal N r (globalCut N p r hN m).val (j.val + 1) -
      cutVal N r (globalCut N p r hN m).val j) := by
  refine ⟨fun t => m.val (partPos N r (globalCut N p r hN m).val
    (globalCut N p r hN m).property ⟨j, t⟩), ?_, ?_⟩
  · intro a b hab
    apply m.property.1
    change cutVal N r (globalCut N p r hN m).val j + a.val <
      cutVal N r (globalCut N p r hN m).val j + b.val
    exact Nat.add_lt_add_left hab _
  · intro t
    have hj := globalCut_block N p r hN m ⟨j, t⟩
    constructor
    · have h := blockId_strict N p hN hpN hp
        (m.val (partPos N r (globalCut N p r hN m).val
          (globalCut N p r hN m).property ⟨j, t⟩)) (m.property.2 _)
      simpa only [hj] using h
    · have h := blockId_hi N p hN
        (m.val (partPos N r (globalCut N p r hN m).val
          (globalCut N p r hN m).property ⟨j, t⟩))
      simpa only [hj] using h
private noncomputable def concatenate (N p r : ℕ) (hN : 0 < N) (c : Cut N r)
    (b : (j : Fin N) → Block N p j
      (cutVal N r c.val (j.val + 1) - cutVal N r c.val j)) : Global p r := by
  let E := partEquiv N r hN c.val c.property
  let f : Fin r → Fin p := fun u => (b (E.symm u).1).val (E.symm u).2
  refine ⟨f, ?_, ?_⟩
  · intro u v huv
    let a := E.symm u
    let d := E.symm v
    have hua : cutVal N r c.val a.1 + a.2.val = u.val :=
      congrArg Fin.val (E.apply_symm_apply u)
    have hvd : cutVal N r c.val d.1 + d.2.val = v.val :=
      congrArg Fin.val (E.apply_symm_apply v)
    have hj : a.1 ≤ d.1 := by
      by_contra h
      have hx := partPos_lt_iff N r c.val c.property d a.1.val
      have ha := a.2.isLt
      have hh := partPos_lt_iff N r c.val c.property a a.1.val
      have hd : d.1.val < a.1.val := by exact lt_of_not_ge h
      have hx' := hx.mpr hd
      change cutVal N r c.val d.1 + d.2.val < cutVal N r c.val a.1 at hx'
      have huv' : u.val < v.val := huv
      omega
    change (b a.1).val a.2 < (b d.1).val d.2
    rcases lt_or_eq_of_le hj with h | h
    · exact interval_order N p a.1.val d.1.val _ _ h
        ((b a.1).property.2 a.2).2 ((b d.1).property.2 d.2).1
    · have ht : a.2.val < d.2.val := by
        have huv' : u.val < v.val := huv
        have he : cutVal N r c.val a.1 = cutVal N r c.val d.1 :=
          congrArg (fun j : Fin N => cutVal N r c.val j) h
        omega
      obtain ⟨aj, ta⟩ := a
      obtain ⟨dj, td⟩ := d
      dsimp at h
      subst dj
      exact (b aj).property.1 ht
  · intro u
    have h := ((b (E.symm u).1).property.2 (E.symm u).2).1
    change 0 < ((b (E.symm u).1).val (E.symm u).2 : ℕ)
    nlinarith

private lemma concatenate_partPos (N p r : ℕ) (hN : 0 < N) (c : Cut N r)
    (b : (j : Fin N) → Block N p j
      (cutVal N r c.val (j.val + 1) - cutVal N r c.val j))
    (z : (j : Fin N) × Fin (cutVal N r c.val (j.val + 1) - cutVal N r c.val j)) :
    (concatenate N p r hN c b).val (partPos N r c.val c.property z) =
      (b z.1).val z.2 := by
  change (b ((partEquiv N r hN c.val c.property).symm
    ((partEquiv N r hN c.val c.property) z)).1).val
    ((partEquiv N r hN c.val c.property).symm
      ((partEquiv N r hN c.val c.property) z)).2 = _
  rw [Equiv.symm_apply_apply]

private lemma blockId_of_interval (N p : ℕ) (hN : 0 < N) (j : Fin N) (v : Fin p)
    (hlo : j.val * p < N * v.val) (hhi : N * v.val < (j.val + 1) * p) :
    blockId N p hN v = j := by
  apply Fin.ext
  have hp : 0 < p := Nat.zero_lt_of_lt v.isLt
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).2 hhi)
  · exact (Nat.le_div_iff_mul_le hp).2 (Nat.le_of_lt hlo)

private lemma concatenate_cut (N p r : ℕ) (hN : 0 < N) (c : Cut N r)
    (b : (j : Fin N) → Block N p j
      (cutVal N r c.val (j.val + 1) - cutVal N r c.val j)) :
    globalCut N p r hN (concatenate N p r hN c b) = c := by
  classical
  apply Subtype.ext
  funext t
  apply Fin.ext
  change (Finset.univ.filter fun u : Fin r =>
    (blockId N p hN ((concatenate N p r hN c b).val u)).val < t.val + 1).card =
    (c.val t).val
  have he : cutVal N r c.val (t.val + 1) = (c.val t).val := by
    have ht := t.isLt
    simp [cutVal, ht]
  have hf : (Finset.univ.filter fun u : Fin r =>
      (blockId N p hN ((concatenate N p r hN c b).val u)).val < t.val + 1) =
      Finset.univ.filter (fun u : Fin r => u.val < (c.val t).val) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨z, rfl⟩ := (partEquiv N r hN c.val c.property).surjective u
    change (blockId N p hN ((concatenate N p r hN c b).val
      (partPos N r c.val c.property z))).val < t.val + 1 ↔ _
    rw [concatenate_partPos, blockId_of_interval N p hN z.1 _
      ((b z.1).property.2 z.2).1 ((b z.1).property.2 z.2).2, ← he]
    exact (partPos_lt_iff N r c.val c.property z (t.val + 1)).symm
  rw [hf]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right (by omega : (c.val t).val ≤ r)]

private lemma concatenate_restrict (N p r : ℕ) (hN : 0 < N) (hpN : N < p)
    (hp : p.Prime) (m : Global p r) :
    concatenate N p r hN (globalCut N p r hN m) (restrictGlobal N p r hN hpN hp m) = m := by
  apply Subtype.ext
  funext u
  obtain ⟨z, rfl⟩ := (partEquiv N r hN (globalCut N p r hN m).val
    (globalCut N p r hN m).property).surjective u
  exact concatenate_partPos N p r hN _ _ z

private noncomputable def decompositionEquiv (N p r : ℕ) (hN : 0 < N) (hpN : N < p)
    (hp : p.Prime) :
    Global p r ≃ ((c : Cut N r) × ((j : Fin N) → Block N p j
      (cutVal N r c.val (j.val + 1) - cutVal N r c.val j))) where
  toFun m := ⟨globalCut N p r hN m, restrictGlobal N p r hN hpN hp m⟩
  invFun v := concatenate N p r hN v.1 v.2
  left_inv := concatenate_restrict N p r hN hpN hp
  right_inv v := by
    obtain ⟨c, b⟩ := v
    apply Sigma.ext (concatenate_cut N p r hN c b)
    apply Function.hfunext
    · rfl
    · intro j j' hj
      cases hj
      have hc := concatenate_cut N p r hN c b
      change restrictGlobal N p r hN hpN hp (concatenate N p r hN c b) j ≍ b j
      generalize hm : concatenate N p r hN c b = m at hc ⊢
      have hp' : ∀ t, m.val (partPos N r c.val c.property ⟨j, t⟩) = (b j).val t := by
        intro t
        rw [← hm]
        exact concatenate_partPos N p r hN c b ⟨j, t⟩
      cases hc
      apply heq_of_eq
      apply Subtype.ext
      funext t
      exact hp' t
open scoped Classical in
private lemma decomposition_sum (N p : ℕ) (hN : 0 < N) (hpN : N < p) (hp : p.Prime)
    (κ : List ℕ) :
    (∑ m : Global p κ.length, ∏ t, (((m.val t : ℕ) : ZMod p)⁻¹) ^ κ.get t) =
      ∑ c : Cut N κ.length, ∏ j : Fin N,
        ∑ b : Block N p j
          (cutVal N κ.length c.val (j.val + 1) - cutVal N κ.length c.val j),
          ∏ t, (((b.val t : ℕ) : ZMod p)⁻¹) ^
            κ.get (partPos N κ.length c.val c.property ⟨j, t⟩) := by
  classical
  rw [Fintype.sum_equiv (decompositionEquiv N p κ.length hN hpN hp)
    (fun m => ∏ t, (((m.val t : ℕ) : ZMod p)⁻¹) ^ κ.get t)
    (fun v => ∏ j : Fin N, ∏ t, (((v.2 j).val t : ℕ) : ZMod p)⁻¹ ^
      κ.get (partPos N κ.length v.1.val v.1.property ⟨j, t⟩)) ?_]
  · rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    exact (Fintype.prod_sum (fun (j : Fin N)
      (b : Block N p j (cutVal N κ.length c.val (j.val + 1) - cutVal N κ.length c.val j)) =>
      ∏ t, (((b.val t : ℕ) : ZMod p)⁻¹) ^
        κ.get (partPos N κ.length c.val c.property ⟨j, t⟩))).symm
  · intro m
    change _ = ∏ j : Fin N, ∏ t,
      (((m.val (partPos N κ.length (globalCut N p κ.length hN m).val
        (globalCut N p κ.length hN m).property ⟨j, t⟩) : ℕ) : ZMod p)⁻¹) ^
        κ.get (partPos N κ.length (globalCut N p κ.length hN m).val
          (globalCut N p κ.length hN m).property ⟨j, t⟩)
    rw [← Fintype.prod_sigma (fun z =>
      (((m.val (partPos N κ.length (globalCut N p κ.length hN m).val
        (globalCut N p κ.length hN m).property z) : ℕ) : ZMod p)⁻¹) ^
      κ.get (partPos N κ.length (globalCut N p κ.length hN m).val
        (globalCut N p κ.length hN m).property z))]
    exact (Fintype.prod_equiv
      (partEquiv N κ.length hN (globalCut N p κ.length hN m).val
        (globalCut N p κ.length hN m).property) _ _ (fun _ => rfl)).symm

private lemma weight_partition (N : ℕ) (hN : 0 < N) (κ : List ℕ) (c : Cut N κ.length) :
    (∑ j : Fin N, ∑ t : Fin
      (cutVal N κ.length c.val (j.val + 1) - cutVal N κ.length c.val j),
      κ.get (partPos N κ.length c.val c.property ⟨j, t⟩)) = κ.sum := by
  rw [← Fintype.sum_sigma (fun z => κ.get (partPos N κ.length c.val c.property z))]
  rw [Fintype.sum_equiv (partEquiv N κ.length hN c.val c.property)
    (fun z => κ.get (partPos N κ.length c.val c.property z)) (fun t => κ.get t)
    (fun _ => rfl)]
  rw [← List.sum_ofFn, List.ofFn_get]
private abbrev Colored (N p j s : ℕ) :=
  {n : Fin s → Fin p // StrictMono n ∧
    ∀ t, 0 < (n t : ℕ) ∧ ((n t : ℕ) : ZMod N) = -(j : ZMod N) * p}

private lemma residue_dvd (N p j n : ℕ) (h : (n : ZMod N) = -(j : ZMod N) * p) :
    N ∣ n + j * p := by
  apply (ZMod.natCast_eq_zero_iff _ _).1
  push_cast
  rw [h]
  ring

private noncomputable def forwardBlock (N p j s : ℕ) (b : Block N p j s) :
    Colored N p j s := by
  refine ⟨fun t => ⟨N * (b.val t).val - j * p, ?_⟩, ?_, ?_⟩
  · have hlo := (b.property.2 t).1
    have hhi := (b.property.2 t).2
    have hh : N * (b.val t).val < j * p + p := by
      simpa only [Nat.add_mul, one_mul] using hhi
    omega
  · intro a c hac
    have hm : (b.val a).val < (b.val c).val := b.property.1 hac
    have hlo := (b.property.2 a).1
    have hN : 0 < N := by nlinarith
    change N * (b.val a).val - j * p < N * (b.val c).val - j * p
    have hh := Nat.mul_lt_mul_of_pos_left hm hN
    omega
  · intro t
    have hlo := (b.property.2 t).1
    constructor
    · change 0 < N * (b.val t).val - j * p
      omega
    · change ((N * (b.val t).val - j * p : ℕ) : ZMod N) = _
      rw [Nat.cast_sub (Nat.le_of_lt hlo)]
      push_cast
      simp

private noncomputable def backwardBlock (N p j s : ℕ) (_hN : 0 < N) (hj : j < N)
    (n : Colored N p j s) : Block N p j s := by
  have hd : ∀ t, N ∣ (n.val t).val + j * p := fun t => residue_dvd _ _ _ _ (n.property.2 t).2
  have he : ∀ t, N * (((n.val t).val + j * p) / N) = (n.val t).val + j * p :=
    fun t => Nat.mul_div_cancel' (hd t)
  have hmem : ∀ t, j * p < N * (((n.val t).val + j * p) / N) ∧
      N * (((n.val t).val + j * p) / N) < (j + 1) * p := by
    intro t
    rw [he t]
    have hpos := (n.property.2 t).1
    have hlt := (n.val t).isLt
    constructor <;> nlinarith
  refine ⟨fun t => ⟨((n.val t).val + j * p) / N, ?_⟩, ?_, hmem⟩
  · have hh := (hmem t).2
    have hbound := Nat.mul_le_mul_right p (show j + 1 ≤ N by omega)
    exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hh hbound)
  · intro a b hab
    have hlt : (n.val a).val < (n.val b).val := n.property.1 hab
    change ((n.val a).val + j * p) / N < ((n.val b).val + j * p) / N
    apply Nat.lt_of_mul_lt_mul_left (a := N)
    rw [he a, he b]
    omega

private noncomputable def rescaleEquiv (N p j s : ℕ) (hN : 0 < N) (hj : j < N) :
    Block N p j s ≃ Colored N p j s where
  toFun := forwardBlock N p j s
  invFun := backwardBlock N p j s hN hj
  left_inv b := by
    apply Subtype.ext
    funext t
    apply Fin.ext
    change (N * (b.val t).val - j * p + j * p) / N = (b.val t).val
    rw [Nat.sub_add_cancel (Nat.le_of_lt (b.property.2 t).1), Nat.mul_div_cancel_left _ hN]
  right_inv n := by
    apply Subtype.ext
    funext t
    apply Fin.ext
    change N * (((n.val t).val + j * p) / N) - j * p = (n.val t).val
    rw [Nat.mul_div_cancel' (residue_dvd _ _ _ _ (n.property.2 t).2)]
    omega

private lemma rescale_term (N p j m n : ℕ) (hp : p.Prime) (hm0 : 0 < m) (hm : m < p)
    (hn0 : 0 < n) (hn : n < p) (h : N * m = n + j * p) (k : ℕ) :
    (m : ZMod p)⁻¹ ^ k = (N : ZMod p) ^ k * (n : ZMod p)⁻¹ ^ k := by
  have hmC : m.Coprime p := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm0 hm)).symm
  have hnC : n.Coprime p := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hn0 hn)).symm
  have hcast : (N : ZMod p) * m = n := by
    have hh := congrArg (fun a : ℕ => (a : ZMod p)) h
    simpa using hh
  have hi : (m : ZMod p)⁻¹ = (N : ZMod p) * (n : ZMod p)⁻¹ := by
    calc
      (m : ZMod p)⁻¹ = (m : ZMod p)⁻¹ * ((n : ZMod p) * (n : ZMod p)⁻¹) := by
        rw [ZMod.coe_mul_inv_eq_one n hnC, mul_one]
      _ = (N : ZMod p) * (n : ZMod p)⁻¹ * ((m : ZMod p) * (m : ZMod p)⁻¹) := by
        rw [← hcast]
        ring
      _ = (N : ZMod p) * (n : ZMod p)⁻¹ := by
        rw [ZMod.coe_mul_inv_eq_one m hmC, mul_one]
  rw [hi, mul_pow]

open scoped Classical in
private lemma perBlock (N p j s : ℕ) (hN : 0 < N) (hj : j < N) (hp : p.Prime)
    (l : Fin s → ℕ) :
    (∑ b : Block N p j s, ∏ t, (((b.val t : ℕ) : ZMod p)⁻¹) ^ l t) =
      (N : ZMod p) ^ (∑ t, l t) *
        coloredFiniteMZV p N l (fun _ => -(j : ZMod N) * p) := by
  classical
  rw [Fintype.sum_equiv (rescaleEquiv N p j s hN hj) _
    (fun n => (N : ZMod p) ^ (∑ t, l t) * ∏ t, (((n.val t : ℕ) : ZMod p)⁻¹) ^ l t) ?_]
  · rw [← Finset.mul_sum]
    congr 1
    unfold coloredFiniteMZV
    exact (Finset.sum_subtype
      (Finset.univ.filter (fun n : Fin s → Fin p => StrictMono n ∧
        ∀ t, 0 < (n t : ℕ) ∧ ((n t : ℕ) : ZMod N) = -(j : ZMod N) * p))
      (by intro n; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun n => ∏ t, (((n t : ℕ) : ZMod p)⁻¹) ^ l t)).symm
  · intro b
    have ht : ∀ t, (((b.val t : ℕ) : ZMod p)⁻¹) ^ l t =
        (N : ZMod p) ^ l t *
          ((((forwardBlock N p j s b).val t : ℕ) : ZMod p)⁻¹) ^ l t := by
      intro t
      apply rescale_term N p j _ _ hp
      · have h := (b.property.2 t).1; nlinarith
      · exact (b.val t).isLt
      · exact ((forwardBlock N p j s b).property.2 t).1
      · exact ((forwardBlock N p j s b).val t).isLt
      · change N * (b.val t).val = N * (b.val t).val - j * p + j * p
        exact (Nat.sub_add_cancel (Nat.le_of_lt (b.property.2 t).1)).symm
    simp_rw [ht]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rfl

private lemma colored_cast (p N s t : ℕ) (h : s = t) (l : Fin t → ℕ) (a : ZMod N) :
    coloredFiniteMZV p N (fun u : Fin s => l (Fin.cast h u)) (fun _ => a) =
      coloredFiniteMZV p N l (fun _ => a) := by
  subst t
  rfl

open scoped Classical in
private lemma perSlice (N p : ℕ) (hN : 0 < N) (hp : p.Prime) (κ : List ℕ)
    (c : Cut N κ.length) (j : Fin N) :
    (∑ b : Block N p j
      (cutVal N κ.length c.val (j.val + 1) - cutVal N κ.length c.val j),
      ∏ t, (((b.val t : ℕ) : ZMod p)⁻¹) ^
        κ.get (partPos N κ.length c.val c.property ⟨j, t⟩)) =
      (N : ZMod p) ^ (∑ t : Fin
        (cutVal N κ.length c.val (j.val + 1) - cutVal N κ.length c.val j),
        κ.get (partPos N κ.length c.val c.property ⟨j, t⟩)) *
        coloredFiniteMZV p N (fun t : Fin (slice κ N c.val j).length =>
          (slice κ N c.val j).get t) (fun _ => -(j.val : ZMod N) * p) := by
  classical
  rw [perBlock N p j _ hN j.isLt hp]
  congr 1
  have hget : (fun t : Fin (slice κ N c.val j).length => (slice κ N c.val j).get t) =
      fun t => κ.get (partPos N κ.length c.val c.property
        ⟨j, Fin.cast (slice_length κ N c.val j) t⟩) := by
    funext t
    simp only [slice, List.get_eq_getElem, List.getElem_take, List.getElem_drop,
      partPos, Fin.val_cast]
  rw [hget]
  exact (colored_cast p N _ _ (slice_length κ N c.val j) _ _).symm

open scoped Classical in
private lemma level_one_sum (p : ℕ) (κ : List ℕ) :
    coloredFiniteMZV p 1 (fun t : Fin κ.length => κ.get t) 0 =
      ∑ m : Global p κ.length, ∏ t, (((m.val t : ℕ) : ZMod p)⁻¹) ^ κ.get t := by
  classical
  unfold coloredFiniteMZV
  have hf : (Finset.univ : Finset (Fin κ.length → Fin p)).filter
      (fun m : Fin κ.length → Fin p => StrictMono m ∧
        ∀ i, 0 < (m i : ℕ) ∧ ((m i : ℕ) : ZMod 1) = (0 : Fin κ.length → ZMod 1) i) =
      Finset.univ.filter (fun m : Fin κ.length → Fin p => StrictMono m ∧ ∀ i, 0 < (m i : ℕ)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hm, h⟩
      exact ⟨hm, fun i => (h i).1⟩
    · rintro ⟨hm, h⟩
      exact ⟨hm, fun i => ⟨h i, Subsingleton.elim _ _⟩⟩
  rw [hf]
  exact Finset.sum_subtype _ (by simp) _
open scoped Classical in
private lemma decomposition_prime (N p : ℕ) (hN : 0 < N) (hpN : N < p) (hp : p.Prime)
    (κ : List ℕ) :
    coloredFiniteMZV p 1 (fun t : Fin κ.length => κ.get t) 0 =
      (N : ZMod p) ^ κ.sum * ∑ c : Cut N κ.length, ∏ j : Fin N,
        coloredFiniteMZV p N (fun t : Fin (slice κ N c.val j).length =>
          (slice κ N c.val j).get t) (fun _ => -(j.val : ZMod N) * p) := by
  classical
  rw [level_one_sum, decomposition_sum N p hN hpN hp κ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [perSlice N p hN hp κ c]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, weight_partition N hN κ c]
open scoped Classical in
/-- **Decomposition of finite multiple zeta values into level-$N$ pieces.** Let $N \ge 1$ and
let $k = (k_1, \dots, k_r)$ be a finite sequence of natural numbers (entries equal to $0$ are
allowed) of weight $w = k_1 + \dots + k_r$. For a prime $p$ put
$\zeta_p(k) = \sum_{0 < m_1 < \dots < m_r < p} m_1^{-k_1} \cdots m_r^{-k_r}$ in
$\mathbb{Z}/p\mathbb{Z}$, and for $0 \le j < N$ and a finite sequence $l$ let
$\zeta^{[j]}_{p,N}(l)$ be the colored finite multiple harmonic sum of level $N$ of $l$ with every
color equal to the class of $-jp$ modulo $N$. Then for all sufficiently large primes $p$
$$
\zeta_p(k) = N^w \sum_{0 \le i_1 \le \dots \le i_{N-1} \le r} \prod_{j=0}^{N-1}
\zeta^{[j]}_{p,N}(k_{i_j + 1}, \dots, k_{i_{j+1}}),
$$
where $i_0 = 0$, $i_N = r$, and $(k_{i_j + 1}, \dots, k_{i_{j+1}})$ is empty when
$i_j = i_{j+1}$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 1 (`integers-2024-A22-prop-1`). -/
public theorem coloredFiniteMZV_one_eq_pow_mul_sum_prod {N : ℕ} (hN : 0 < N)
    (κ : List ℕ) :
    ∀ᶠ p in atTop, p.Prime →
      coloredFiniteMZV p 1 (fun t : Fin κ.length => κ.get t) 0 =
        (N : ZMod p) ^ κ.sum *
          ∑ i ∈ (Finset.univ : Finset (Fin (N - 1) → Fin (κ.length + 1))).filter Monotone,
            ∏ j : Fin N,
              let e : ℕ → ℕ := fun t =>
                if t = 0 then 0 else if h : t - 1 < N - 1 then (i ⟨t - 1, h⟩ : ℕ) else κ.length
              let sub := (κ.drop (e j)).take (e ((j : ℕ) + 1) - e j)
              coloredFiniteMZV p N (fun t : Fin sub.length => sub.get t)
                (fun _ => -((j : ℕ) : ZMod N) * p) := by
  classical
  filter_upwards [eventually_gt_atTop N] with p hpN hp
  rw [decomposition_prime N p hN hpN hp κ]
  congr 1
  exact (Finset.sum_subtype
    ((Finset.univ : Finset (Fin (N - 1) → Fin (κ.length + 1))).filter Monotone)
    (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun i => ∏ j : Fin N, coloredFiniteMZV p N
      (fun t : Fin (slice κ N i j).length => (slice κ N i j).get t)
      (fun _ => -(j.val : ZMod N) * p))).symm

end
end MetaMathlibExt
