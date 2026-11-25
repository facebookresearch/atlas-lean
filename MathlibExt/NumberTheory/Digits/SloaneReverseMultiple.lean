/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace MetaMathlibExt

/-- **Sloane's endpoint formula for reverse multiples.** Let $g$ and $k$ be integers with
$2 \le k < g$, and let $N = (a_n a_{n-1} \cdots a_0)_g$ have base-$g$ digits
$a_0, \dots, a_n \in \{0, \dots, g - 1\}$, with units digit $a_0$ and leading digit $a_n \ne 0$.
Suppose $N$ is a $(g, k)$ reverse multiple, that is, $k N = (a_0 a_1 \cdots a_n)_g$, and that
$a_0 + a_n = g$. Then $(k + 1) a_n = g$; in particular $k + 1$ divides $g$ and
$a_n = g / (k + 1)$.

Source: L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer
Sequences 18 (2015), Article 15.9.7, Corollary `cor:lastdig1089` (Sloane's
Conjecture 3.5) and proof, lines 418–424,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>.
Proves `Wanted` entry `sloane_reverse_multiple_endpoint`.
-/
theorem sloane_reverse_multiple_endpoint
    (g k a₀ aLast : ℕ) (digits : List ℕ)
    (hk : 2 ≤ k) (hkg : k < g)
    (hdigits : ∀ d ∈ digits, d < g)
    (hunits : digits.head? = some a₀)
    (hleading : digits.getLast? = some aLast)
    (hleading_ne : aLast ≠ 0)
    (hreverse : k * Nat.ofDigits g digits = Nat.ofDigits g digits.reverse)
    (hendpoint_sum : a₀ + aLast = g) :
    (k + 1) * aLast = g ∧ aLast = g / (k + 1) ∧ k + 1 ∣ g := by
  have hg1 : 1 < g := by omega
  have hg0 : 0 < g := by omega
  obtain ⟨t, hDt⟩ := List.head?_eq_some_iff.mp hunits
  obtain ⟨init, hDi⟩ := List.getLast?_eq_some_iff.mp hleading
  have ha₀mem : a₀ ∈ digits := by rw [hDt]; exact List.mem_cons_self
  have haLastmem : aLast ∈ digits := by
    rw [hDi]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have ha₀lt : a₀ < g := hdigits _ ha₀mem
  have haLastlt : aLast < g := hdigits _ haLastmem
  have haLastpos : 0 < aLast := Nat.pos_of_ne_zero hleading_ne
  -- Low-end decompositions.
  have hN : Nat.ofDigits g digits = a₀ + g * Nat.ofDigits g t := by
    rw [hDt, Nat.ofDigits_cons]
  have hR : digits.reverse = aLast :: init.reverse := by
    rw [hDi, List.reverse_append]; simp
  have hM : Nat.ofDigits g digits.reverse = aLast + g * Nat.ofDigits g init.reverse := by
    rw [hR, Nat.ofDigits_cons]
  -- Divisibility: g ∣ (k+1) * aLast via residues mod g.
  have hNmod : Nat.ofDigits g digits ≡ a₀ [MOD g] := by
    show Nat.ofDigits g digits % g = a₀ % g
    rw [hN, Nat.add_mul_mod_self_left]
  have hMmod : Nat.ofDigits g digits.reverse ≡ aLast [MOD g] := by
    show Nat.ofDigits g digits.reverse % g = aLast % g
    rw [hM, Nat.add_mul_mod_self_left]
  have hkm : k * a₀ ≡ aLast [MOD g] := by
    have h1 : k * Nat.ofDigits g digits ≡ k * a₀ [MOD g] :=
      Nat.ModEq.mul_left k hNmod
    rw [hreverse] at h1
    exact h1.symm.trans hMmod
  have hkey : (k + 1) * aLast ≡ 0 [MOD g] := by
    have h2 := Nat.ModEq.add_right (k * aLast) hkm
    have hL : k * a₀ + k * aLast = k * g := by
      rw [← Nat.mul_add, hendpoint_sum]
    have hRhs : aLast + k * aLast = (k + 1) * aLast := by ring
    rw [hL] at h2
    rw [hRhs] at h2
    have hz : k * g ≡ 0 [MOD g] :=
      Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.mul_left (dvd_refl g) k)
    exact h2.symm.trans hz
  have hdvd : g ∣ (k + 1) * aLast := Nat.modEq_zero_iff_dvd.mp hkey
  -- High-end bound: (k+1) * aLast ≤ g.
  have hlen : t.length = init.length := by
    have h := congrArg List.length (hDt.symm.trans hDi)
    simp at h
    omega
  have hlenr : (t.reverse).length = init.length := by simp [hlen]
  have hmem_tr : ∀ x ∈ t.reverse, x < g := by
    intro x hx
    have hx' : x ∈ t := List.mem_reverse.mp hx
    have hx'' : x ∈ digits := by
      rw [hDt]; exact List.mem_cons_of_mem _ hx'
    exact hdigits x hx''
  have hR1 : digits.reverse = t.reverse ++ [a₀] := by
    rw [hDt, List.reverse_cons]
  have hMhi : Nat.ofDigits g digits.reverse
      = Nat.ofDigits g t.reverse + g ^ (t.reverse).length * a₀ := by
    rw [hR1, Nat.ofDigits_append, Nat.ofDigits_singleton]
  have hNlo : Nat.ofDigits g digits
      = Nat.ofDigits g init + g ^ init.length * aLast := by
    rw [hDi, Nat.ofDigits_append, Nat.ofDigits_singleton]
  have hpow : 0 < g ^ init.length := pow_pos hg0 _
  have hNge : g ^ init.length * aLast ≤ Nat.ofDigits g digits := by
    rw [hNlo]; exact Nat.le_add_left _ _
  have hstep1 : (k * aLast) * g ^ init.length ≤ Nat.ofDigits g digits.reverse := by
    have h1 : k * (g ^ init.length * aLast) ≤ k * Nat.ofDigits g digits :=
      Nat.mul_le_mul_left k hNge
    have h2 : k * (g ^ init.length * aLast) = (k * aLast) * g ^ init.length := by
      ring
    rw [h2] at h1
    rw [hreverse] at h1
    exact h1
  have hMlt : Nat.ofDigits g t.reverse + g ^ (t.reverse).length * a₀
      < (a₀ + 1) * g ^ init.length := by
    have hlt : Nat.ofDigits g t.reverse < g ^ (t.reverse).length :=
      Nat.ofDigits_lt_base_pow_length hg1 hmem_tr
    have hring : (a₀ + 1) * g ^ init.length
        = g ^ init.length + g ^ init.length * a₀ := by ring
    rw [hring, ← hlenr]
    exact Nat.add_lt_add_right hlt _
  have hlt2 : (k * aLast) * g ^ init.length < (a₀ + 1) * g ^ init.length := by
    rw [hMhi] at hstep1
    exact lt_of_le_of_lt hstep1 hMlt
  have hfin : k * aLast < a₀ + 1 := lt_of_mul_lt_mul_right hlt2 hpow.le
  have hle2 : k * aLast ≤ a₀ := Nat.lt_succ_iff.mp hfin
  have hXle : (k + 1) * aLast ≤ g := by
    have h1 : k * aLast + aLast ≤ a₀ + aLast := Nat.add_le_add_right hle2 _
    rw [hendpoint_sum] at h1
    have h2 : (k + 1) * aLast = k * aLast + aLast := by ring
    rw [h2]
    exact h1
  -- Assembly.
  have hXpos : 0 < (k + 1) * aLast := Nat.mul_pos (by omega) haLastpos
  have hgle : g ≤ (k + 1) * aLast := Nat.le_of_dvd hXpos hdvd
  have heq : (k + 1) * aLast = g := le_antisymm hXle hgle
  have hpos1 : 0 < k + 1 := by omega
  have hdiv : aLast = g / (k + 1) := by
    rw [← heq, Nat.mul_div_cancel_left _ hpos1]
  have hdvd2 : k + 1 ∣ g := by rw [← heq]; exact dvd_mul_right _ _
  exact ⟨heq, hdiv, hdvd2⟩

end MetaMathlibExt

end
