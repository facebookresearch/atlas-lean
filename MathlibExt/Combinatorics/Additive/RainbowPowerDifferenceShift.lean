/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Card

/-!
# Shifts of monochromatic strings in rainbow-free colorings

In a coloring of the positive integers by three distinct colors `R`, `B`, and `G` that is
rainbow-free for `x = y + z ^ k`, suppose `R` occurs in every bichromatic interval. For `j > 0`
colored `B` and an interval of length `ℓ` starting at `i > 0` colored `G`, shifting right by
`j ^ k` gives a monochromatic interval colored `B` or `G`. The same holds for the left shift
when `j ^ k < i`, so the shifted interval starts at a positive integer. The empty interval
satisfies the conclusion vacuously. Exactness and maximality of the original interval are not
needed, and the argument works for every natural exponent.

## References

* Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and
  Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, pp. 1–16, Lemma 2 (p. 3).
* Tong Zhan, *On Rainbow Solutions to an Equation with a Quadratic Term*, INTEGERS 9 (2009),
  Article A49, pp. 655–670, Lemma 4 (p. 657), the quadratic precursor.
-/

namespace MetaMathlibExt

/-- **Shifting monochromatic strings by $k$-th powers.** Let $k$ be a natural number and let $c$
be a coloring of the positive integers by three distinct colors $R$, $B$, $G$ with no rainbow
solution of $x - y = z^k$: there are no positive integers $x, y, z$ with $x = y + z^k$ and
$c(x)$, $c(y)$, $c(z)$ pairwise distinct. Assume that $R$ is dominant: for all positive integers
$i$ and all $\ell \ge 0$, if $c$ takes exactly two colors on $\{i, i + 1, \dots, i + \ell - 1\}$,
then one of them is $R$. Let $j$ be a positive integer with $c(j) = B$, and let $i \ge 1$ and
$\ell \ge 0$ be such that $c(i + t) = G$ for all $0 \le t < \ell$. Then there is a color
$e \in \{B, G\}$ with $c(i + j^k + t) = e$ for all $0 \le t < \ell$, and, if $j^k < i$, there
is a color $e' \in \{B, G\}$ with $c(i - j^k + t) = e'$ for all $0 \le t < \ell$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 2
(`integers-2024-A105-lem-2`). -/
public theorem monochromatic_shift_of_rainbowFree_powDiff (k : ℕ) (c : ℕ → Fin 3)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (R B G : Fin 3) (hRB : R ≠ B) (hRG : R ≠ G) (hBG : B ≠ G)
    (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      R ∈ (Finset.Ico i (i + ℓ)).image c)
    (j : ℕ) (hj : 0 < j) (hcj : c j = B) (i ℓ : ℕ) (hi : 0 < i)
    (hG : ∀ t < ℓ, c (i + t) = G) :
    (∃ e : Fin 3, (e = B ∨ e = G) ∧ ∀ t < ℓ, c (i + j ^ k + t) = e) ∧
      (j ^ k < i → ∃ e : Fin 3, (e = B ∨ e = G) ∧ ∀ t < ℓ, c (i - j ^ k + t) = e) := by
  have hall : ({R, B, G} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hRB, hRG, hBG]
  have hcolors {a : Fin 3} (ha : a ≠ R) : a = B ∨ a = G := by
    have hm : a ∈ ({R, B, G} : Finset (Fin 3)) := hall.symm ▸ Finset.mem_univ a
    simpa [ha] using hm
  -- Dominance makes an interval omitting `R` monochromatic.
  have mono (s : ℕ) (hs : 0 < s) (h : ∀ t < ℓ, c (s + t) ≠ R) :
      ∃ e : Fin 3, (e = B ∨ e = G) ∧ ∀ t < ℓ, c (s + t) = e := by
    by_cases hℓ : ℓ = 0
    · exact ⟨B, Or.inl rfl, by simp [hℓ]⟩
    let colors := (Finset.Ico s (s + ℓ)).image c
    have hmem (t : ℕ) (ht : t < ℓ) : c (s + t) ∈ colors :=
      Finset.mem_image.mpr ⟨s + t, Finset.mem_Ico.mpr (by omega), rfl⟩
    have hne {a : Fin 3} (ha : a ∈ colors) : a ≠ R := by
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hsn, hsn'⟩ := Finset.mem_Ico.mp hn
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hsn
      exact h t (by omega)
    have hsub : colors ⊆ {B, G} := by
      intro a ha
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcolors (hne ha)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hBG] at hle
    have htwo : colors.card ≠ 2 := fun hc => hne (hdom s ℓ hs hc) rfl
    have hcard : colors.card ≤ 1 := by omega
    have hstart : c s ∈ colors := by simpa only [Nat.add_zero] using hmem 0 (by omega)
    exact ⟨c s, hcolors (hne hstart), fun t ht =>
      Finset.card_le_one_iff.mp hcard (hmem t ht) hstart⟩
  constructor
  · apply mono (i + j ^ k) (by omega)
    intro t ht hR
    apply hrf (i + j ^ k + t) (i + t) j (by omega) (by omega) hj (by omega)
    rw [hR, hG t ht, hcj]
    exact ⟨hRG, hBG.symm, hRB⟩
  · intro hleft
    apply mono (i - j ^ k) (by omega)
    intro t ht hR
    apply hrf (i + t) (i - j ^ k + t) j (by omega) (by omega) hj (by omega)
    rw [hG t ht, hR, hcj]
    exact ⟨hRG.symm, hRB, hBG.symm⟩

end MetaMathlibExt
