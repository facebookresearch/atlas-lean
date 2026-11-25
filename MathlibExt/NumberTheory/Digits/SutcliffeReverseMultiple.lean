/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/-- **Sutcliffe's theorem on two- and three-digit reverse multiples.** Let $g$ and $k$ be
integers with $2 \le k < g$, and let $a$ and $b$ be base-$g$ digits, $0 \le a, b < g$, with
$a \ne 0$, such that $(a\,b)_g$ is a $(g, k)$ reverse multiple, that is,
$k (a g + b) = b g + a$. Then $a + b < g$, so $a + b$ is a base-$g$ digit, and
$(a\,(a + b)\,b)_g$ is again a $(g, k)$ reverse multiple, that is,
$k (a g^2 + (a + b) g + b) = b g^2 + (a + b) g + a$.

This is the forward implication of Sutcliffe's theorem; the converse is not included.

Source: L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer
Sequences 18 (2015), Article 15.9.7, Remark `rem:truncate` (quoting
Sutcliffe's Theorem 3), lines 203–205,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>.
Proves `Wanted` entry `sutcliffe_two_to_three_digit_reverse_multiple`.
-/
theorem sutcliffe_two_to_three_digit_reverse_multiple
    (g k a b : ℕ)
    (hk : 2 ≤ k) (hkg : k < g)
    (ha : a ≠ 0) (hag : a < g) (hbg : b < g)
    (hreverse : k * (a * g + b) = b * g + a) :
    a + b < g ∧
      k * (a * g ^ 2 + (a + b) * g + b) =
        b * g ^ 2 + (a + b) * g + a := by
  -- Write k = j + 1 so that `k - 1` never appears as truncated subtraction.
  have hex : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ := hex
  have ha1 : 1 ≤ a := by omega
  have hj1 : 1 ≤ j := by omega
  -- Key carry fact: k * a ≤ b (from k * a * g < g * (b + 1)).
  have hkab : (j + 1) * a ≤ b := by
    by_contra h
    push Not at h
    have h1 : b + 1 ≤ (j + 1) * a := by omega
    have h2 : (b + 1) * g ≤ ((j + 1) * a) * g := by gcongr
    have h3 : (j + 1) * (a * g + b) = ((j + 1) * a) * g + (j + 1) * b := by
      ring
    rw [h3] at hreverse
    have h4 : (b + 1) * g = b * g + g := by ring
    rw [h4] at h2
    omega
  -- Write b = k * a + e (carry) and g = k + d (both Nat-subtraction free).
  have heb : ∃ e, b = (j + 1) * a + e := ⟨b - (j + 1) * a, by omega⟩
  obtain ⟨e, he⟩ := heb
  have hgd : ∃ d, g = (j + 1) + d := ⟨g - (j + 1), by omega⟩
  obtain ⟨d, hd⟩ := hgd
  rw [hd] at hag hbg hkg hreverse ⊢
  rw [he] at hbg hreverse ⊢
  have hd1 : 1 ≤ d := by omega
  -- The hypothesis collapses to k ^ 2 * a = e * d + a.
  have hmain : (j + 1) * (j + 1) * a = e * d + a := by
    linear_combination hreverse
  -- The carry e is smaller than k.
  have hek : e < j + 1 := by
    by_contra h
    push Not at h
    have h1 : (j + 1) * a < d := by omega
    have hpos : 0 < j + 1 := by omega
    have h2 : (j + 1) * ((j + 1) * a) < (j + 1) * d := by gcongr
    have h3 : (j + 1) * ((j + 1) * a) = (j + 1) * (j + 1) * a := by ring
    rw [h3] at h2
    have h4 : (j + 1) * d ≤ e * d := by gcongr
    omega
  -- Hence a * (k + 1) * (k - 1) = e * d with `k - 1` spelled `j`.
  have hTe : a * (j + 1 + 1) * j = e * d := by
    linear_combination hmain
  have hej : e ≤ j := by omega
  -- Cancel j to get a * (k + 1) ≤ d.
  have hT : a * (j + 1 + 1) ≤ d := by
    by_contra h
    push Not at h
    have h6 : d * j < a * (j + 1 + 1) * j := by gcongr
    have h5 : e * d ≤ j * d := by gcongr
    have h7 : j * d = d * j := by ring
    omega
  refine ⟨?_, ?_⟩
  · have h8 : a + ((j + 1) * a + e) = a * (j + 1 + 1) + e := by ring
    omega
  · linear_combination (1 + (j + 1 + d)) * hmain

end MetaMathlibExt
