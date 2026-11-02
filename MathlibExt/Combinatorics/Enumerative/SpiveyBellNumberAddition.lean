/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

open scoped BigOperators


private theorem stirling_collect (m : ℕ) (F : ℕ → ℕ) :
    (∑ j ∈ Finset.range (m + 2), (m + 1).stirlingSecond j * F j)
    = ∑ j ∈ Finset.range (m + 1), m.stirlingSecond j * (j * F j + F (j + 1)) := by
  have hre : (∑ j ∈ Finset.range (m + 1), (j + 1) * m.stirlingSecond (j + 1) * F (j + 1))
      = ∑ j ∈ Finset.range (m + 1), j * m.stirlingSecond j * F j := by
    have h1 := Finset.sum_range_succ' (fun i => i * m.stirlingSecond i * F i) (m + 1)
    have h2 := Finset.sum_range_succ (fun i => i * m.stirlingSecond i * F i) (m + 1)
    have hvan0 : 0 * m.stirlingSecond 0 * F 0 = 0 := by simp
    have hvan1 : (m + 1) * m.stirlingSecond (m + 1) * F (m + 1) = 0 := by
      simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m)]
    rw [hvan0] at h1
    rw [hvan1] at h2
    omega
  rw [Finset.sum_range_succ' (fun j => (m + 1).stirlingSecond j * F j) (m + 1)]
  have hvanS : (m + 1).stirlingSecond 0 * F 0 = 0 := by
    simp [Nat.stirlingSecond_succ_zero]
  rw [hvanS, add_zero]
  have hexpand : ∀ j ∈ Finset.range (m + 1),
      (m + 1).stirlingSecond (j + 1) * F (j + 1)
      = ((j + 1) * m.stirlingSecond (j + 1) * F (j + 1) + m.stirlingSecond j * F (j + 1)) := by
    intro j _
    rw [Nat.stirlingSecond_succ_succ]
    ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib]
  have hsplit : (∑ j ∈ Finset.range (m + 1), m.stirlingSecond j * (j * F j + F (j + 1)))
      = (∑ j ∈ Finset.range (m + 1), m.stirlingSecond j * (j * F j))
        + (∑ j ∈ Finset.range (m + 1), m.stirlingSecond j * F (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit, hre]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring


private theorem bell_succ_range (n : ℕ) :
    (n + 1).bell = ∑ k ∈ Finset.range (n + 1), n.choose k * k.bell := by
  have hanti := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => n.choose a * b.bell) n
  have hrefl : (∑ k ∈ Finset.range n.succ, n.choose k * (n - k).bell)
      = ∑ k ∈ Finset.range (n + 1), n.choose k * k.bell := by
    rw [← Finset.sum_range_reflect (fun k => n.choose k * k.bell) (n + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkn : k ≤ n := by omega
    have h1 : n + 1 - 1 - k = n - k := by omega
    rw [h1, Nat.choose_symm hkn]
  exact (Nat.bell_succ' n).trans (hanti.trans hrefl)

private theorem key_identity (j n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), j ^ (n + 1 - k) * (n + 1).choose k * k.bell)
      = j * (∑ k ∈ Finset.range (n + 1), j ^ (n - k) * n.choose k * k.bell)
        + (∑ k ∈ Finset.range (n + 1), (j + 1) ^ (n - k) * n.choose k * k.bell) := by
  have hswap : (∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1),
        j ^ (n - k) * n.choose k * (k.choose i * i.bell))
      = ∑ i ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n - i + 1),
        j ^ (n - i - t) * n.choose i * ((n - i).choose t * i.bell) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => (⟨p.2, p.1 - p.2⟩ : Σ _ : ℕ, ℕ))
    · intro a ha
      simp only [Finset.mem_sigma, Finset.mem_range] at ha
      obtain ⟨h1, h2⟩ := ha
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · have hlt : a.2 < n + 1 := by omega
        exact Finset.mem_range.mpr hlt
      · have hlt : a.1 - a.2 < n - a.2 + 1 := by omega
        exact Finset.mem_range.mpr hlt
    · intro a₁ ha₁ a₂ ha₂ heq
      obtain ⟨k1, i1⟩ := a₁
      obtain ⟨k2, i2⟩ := a₂
      simp only [Finset.mem_sigma, Finset.mem_range] at ha₁ ha₂
      have e1 : i1 = i2 := congrArg Sigma.fst heq
      have e2 : k1 - i1 = k2 - i2 := congrArg Sigma.snd heq
      have hk : k1 = k2 := by omega
      subst hk
      subst e1
      rfl
    · intro b hb
      obtain ⟨k, t⟩ := b
      simp only [Finset.mem_sigma, Finset.mem_range] at hb
      refine ⟨⟨k + t, k⟩, ?_, ?_⟩
      · have hmem : k + t < n + 1 ∧ k < k + t + 1 := by constructor <;> omega
        exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hmem.1, Finset.mem_range.mpr hmem.2⟩
      · change (⟨k, k + t - k⟩ : Σ _ : ℕ, ℕ) = ⟨k, t⟩
        rw [Nat.add_sub_cancel_left]
    · intro a ha
      simp only [Finset.mem_sigma, Finset.mem_range] at ha
      obtain ⟨h1, h2⟩ := ha
      have hle : a.2 ≤ a.1 := by omega
      have hexp : n - a.2 - (a.1 - a.2) = n - a.1 := by omega
      have hch := Nat.choose_mul (n := n) (k := a.1) (s := a.2) hle
      have hrw : j ^ (n - a.1) * n.choose a.1 * (a.1.choose a.2 * a.2.bell)
          = (n.choose a.1 * a.1.choose a.2) * (j ^ (n - a.1) * a.2.bell) := by ring
      change j ^ (n - a.1) * n.choose a.1 * (a.1.choose a.2 * a.2.bell)
         = j ^ (n - a.2 - (a.1 - a.2)) * n.choose a.2 * ((n - a.2).choose (a.1 - a.2) * a.2.bell)
      rw [hexp, hrw, hch]
      ring
  have hmid : (∑ k ∈ Finset.range (n + 1), j ^ (n - k) * n.choose k * (k + 1).bell)
      = ∑ k ∈ Finset.range (n + 1), (j + 1) ^ (n - k) * n.choose k * k.bell := by
    have e1 : (∑ k ∈ Finset.range (n + 1), j ^ (n - k) * n.choose k * (k + 1).bell)
        = ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1),
          j ^ (n - k) * n.choose k * (k.choose i * i.bell) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [bell_succ_range k, Finset.mul_sum]
    rw [e1, hswap]
    apply Finset.sum_congr rfl
    intro i hi
    have e2 : (∑ t ∈ Finset.range (n - i + 1),
          j ^ (n - i - t) * n.choose i * ((n - i).choose t * i.bell))
        = (n.choose i * i.bell) * (∑ t ∈ Finset.range (n - i + 1),
          j ^ (n - i - t) * (n - i).choose t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [e2]
    have e3 : (∑ t ∈ Finset.range (n - i + 1), j ^ (n - i - t) * (n - i).choose t)
        = (j + 1) ^ (n - i) := by
      have hb := add_pow (1 : ℕ) j (n - i)
      rw [show (1 : ℕ) + j = j + 1 from add_comm _ _] at hb
      simp only [Nat.cast_id] at hb
      rw [hb]
      apply Finset.sum_congr rfl
      intro t _
      simp
    rw [e3]
    ring
  have hpeel : (∑ k ∈ Finset.range (n + 2), j ^ (n + 1 - k) * (n + 1).choose k * k.bell)
      = (∑ k ∈ Finset.range (n + 1),
          (j ^ (n - k) * n.choose k * (k + 1).bell
            + j ^ (n - k) * n.choose (k + 1) * (k + 1).bell))
        + j ^ (n + 1) := by
    have h2 : n + 2 = (n + 1) + 1 := by omega
    have h := Finset.sum_range_succ'
      (fun k => j ^ (n + 1 - k) * (n + 1).choose k * k.bell) (n + 1)
    have h0 : j ^ (n + 1 - 0) * (n + 1).choose 0 * Nat.bell 0
        = j ^ (n + 1) := by simp
    rw [h0] at h
    rw [h2, h]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    show j ^ (n + 1 - (k + 1)) * (n + 1).choose (k + 1) * (k + 1).bell = _
    have hexp : n + 1 - (k + 1) = n - k := by omega
    rw [hexp, Nat.choose_succ_succ']
    ring
  have elast : j ^ (n - n) * n.choose (n + 1) * (n + 1).bell = 0 := by simp
  have eL : (∑ k ∈ Finset.range (n + 1), j ^ (n - k) * n.choose (k + 1) * (k + 1).bell)
      = (∑ k ∈ Finset.range n, j ^ (n - k) * n.choose (k + 1) * (k + 1).bell)
        + j ^ (n - n) * n.choose (n + 1) * (n + 1).bell := by
    rw [Finset.sum_range_succ]
  have eR : (∑ k ∈ Finset.range (n + 1), j * (j ^ (n - k) * n.choose k * k.bell))
      = (∑ k ∈ Finset.range n, j ^ (n - k) * n.choose (k + 1) * (k + 1).bell)
        + j ^ (n + 1) := by
    rw [Finset.sum_range_succ' (fun k => j * (j ^ (n - k) * n.choose k * k.bell)) n]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      show j * (j ^ (n - (k + 1)) * n.choose (k + 1) * (k + 1).bell) = _
      have hkn : k < n := Finset.mem_range.mp hk
      have e : n - k = (n - (k + 1)) + 1 := by omega
      rw [e, pow_succ']
      ring
    · show j * (j ^ (n - 0) * n.choose 0 * Nat.bell 0) = j ^ (n + 1)
      simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.bell_zero, mul_one]
      exact (pow_succ' j n).symm
  have hthird : (∑ k ∈ Finset.range (n + 1), j ^ (n - k) * n.choose (k + 1) * (k + 1).bell)
      + j ^ (n + 1)
      = j * (∑ k ∈ Finset.range (n + 1), j ^ (n - k) * n.choose k * k.bell) := by
    rw [eL, elast, add_zero, Finset.mul_sum, eR]
  rw [hpeel, Finset.sum_add_distrib, hmid, add_assoc, hthird]
  exact add_comm _ _

/-- **Spivey's Bell number formula.** For all natural numbers $m$ and $n$,

$$B_{n+m} = \sum_{j=0}^{m} \sum_{k=0}^{n} j^{n-k} \, S(m, j) \binom{n}{k} B_k,$$

where $B_k$ is the $k$-th Bell number, $S(m, j)$ is the Stirling number of the second kind, and
$0^0 = 1$.

Source: Michael Z. Spivey, *A Generalized Recurrence for Bell Numbers*,
Journal of Integer Sequences 11 (2008), Article 08.2.5, equation `Bell_Gen`,
lines 113–117,
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Spivey/spivey25.tex>.

Proves `Wanted` entry `spivey_bell_number_add`.
-/
theorem spivey_bell_number_add (m n : ℕ) : (n + m).bell = ∑ j ∈ Finset.range (m + 1), ∑ k ∈
  Finset.range (n + 1), j ^ (n - k) * m.stirlingSecond j * n.choose k * k.bell := by
  revert n
  induction m with
  | zero =>
    intro n
    simp only [Nat.add_zero, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.stirlingSecond_zero]
    rw [Finset.sum_eq_single n]
    · simp
    · intro k hk hkn
      have hkk : k < n := by
        simp only [Finset.mem_range] at hk
        omega
      have hpos : 0 < n - k := by omega
      simp [Nat.zero_pow hpos]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hcon
  | succ m ih =>
    intro n
    have hIH := ih (n + 1)
    rw [show n + 1 + 1 = n + 2 from by omega] at hIH
    rw [show n + (m + 1) = (n + 1) + m from by omega, hIH,
      show m + 1 + 1 = m + 2 from by omega]
    have step1 : (∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 2),
          j ^ (n + 1 - k) * m.stirlingSecond j * (n + 1).choose k * k.bell)
        = ∑ j ∈ Finset.range (m + 1),
          m.stirlingSecond j * (∑ k ∈ Finset.range (n + 2),
            j ^ (n + 1 - k) * (n + 1).choose k * k.bell) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have step2 : (∑ j ∈ Finset.range (m + 1),
          m.stirlingSecond j * (∑ k ∈ Finset.range (n + 2),
            j ^ (n + 1 - k) * (n + 1).choose k * k.bell))
        = ∑ j ∈ Finset.range (m + 1),
          m.stirlingSecond j * (j * (∑ k ∈ Finset.range (n + 1),
            j ^ (n - k) * n.choose k * k.bell)
            + (∑ k ∈ Finset.range (n + 1), (j + 1) ^ (n - k) * n.choose k * k.bell)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [key_identity j n]
    have step3 : (∑ j ∈ Finset.range (m + 1),
          m.stirlingSecond j * (j * (∑ k ∈ Finset.range (n + 1),
            j ^ (n - k) * n.choose k * k.bell)
            + (∑ k ∈ Finset.range (n + 1), (j + 1) ^ (n - k) * n.choose k * k.bell)))
        = ∑ j ∈ Finset.range (m + 2),
          (m + 1).stirlingSecond j * (∑ k ∈ Finset.range (n + 1),
            j ^ (n - k) * n.choose k * k.bell) := by
      exact (stirling_collect m (fun j => ∑ k ∈ Finset.range (n + 1),
        j ^ (n - k) * n.choose k * k.bell)).symm
    have step4 : (∑ j ∈ Finset.range (m + 2),
          (m + 1).stirlingSecond j * (∑ k ∈ Finset.range (n + 1),
            j ^ (n - k) * n.choose k * k.bell))
        = ∑ j ∈ Finset.range (m + 2), ∑ k ∈ Finset.range (n + 1),
          j ^ (n - k) * (m + 1).stirlingSecond j * n.choose k * k.bell := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    exact step1.trans (step2.trans (step3.trans step4))

end

/-- **Spivey's recurrence for Bell numbers.** For all natural numbers $n$ and $m$,

$$B_{n+m} = \sum_{k=0}^{n} \sum_{j=0}^{m} j^{n-k} \, S(m, j) \binom{n}{k} B_k,$$

where $B_k$ is the $k$-th Bell number, $S(m, j)$ is the Stirling number of the second kind, and
$0^0 = 1$. This is Spivey's Bell number formula with the two finite sums interchanged.

Source: Jacob Katriel, "On a Generalized Recurrence for Bell Numbers",
Journal of Integer Sequences 11 (2008), Article 08.3.8, equation (Spivey),
lines 77–81,
https://cs.uwaterloo.ca/journals/JIS/VOL11/Katriel/katriel6.tex
(quoting Michael Z. Spivey, "A generalized recurrence for Bell numbers",
Journal of Integer Sequences 11 (2008), Article 08.2.5).

Proves `Wanted` entry `spivey_bell_recurrence`.
-/
theorem spivey_bell_recurrence (n m : ℕ) :
    Nat.bell (n + m) =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        j ^ (n - k) * Nat.stirlingSecond m j * Nat.choose n k * Nat.bell k := by
  exact (spivey_bell_number_add m n).trans Finset.sum_comm

end MetaMathlibExt
