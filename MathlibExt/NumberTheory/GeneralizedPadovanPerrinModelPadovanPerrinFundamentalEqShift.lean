/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion

/-!
# Shift property of the generalized Padovan–Perrin fundamental system

For `p + 1 ≤ j ≤ s + p - 1`, the `j`-th fundamental sequence is the shift of the last one:
`padovanPerrinFundamental_eq_shift` proves `v⁽ʲ⁾ n = v⁽ˢ⁺ᵖ⁾ (n + s + p - j)` for every `n`,
and unfolds it once through the recurrence for `n ≥ j`.

## References

* Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
  *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*,
  INTEGERS 24 (2024), Article A49, Proposition 2 (`integers-2024-A49-prop-2`).
-/

@[expose] public section

namespace MetaMathlibExt

private theorem padovanPerrin_isSolution_shift {R : Type*} [CommSemiring R]
    (E : LinearRecurrence R) (u : ℕ → R) (h : E.IsSolution u) (d : ℕ) :
    E.IsSolution (fun n => u (n + d)) := by
  intro n
  have h1 := h (n + d)
  have e1 : n + E.order + d = n + d + E.order := by omega
  have e2 : ∀ i : Fin E.order, n + d + (i : ℕ) = n + (i : ℕ) + d := fun i => by omega
  dsimp only
  rw [e1, h1]
  congr 1
  ext i
  rw [e2 i]

/-- **Shift property of the generalized Padovan–Perrin fundamental system.** Let $R$ be a
commutative ring, $k_1, k_2 \in R$, and let $p, s, j$ be natural numbers with $p \ge 1$ and
$p + 1 \le j \le s + p - 1$. Write $v^{(\ell)}$ for the $\ell$-th sequence of the Fibonacci
fundamental system of the $([k]; p; s)$-Padovan–Perrin recurrence. Then
$v^{(j)}_n = v^{(s+p)}_{n+s+p-j}$ for every $n \ge 0$, and
$v^{(j)}_n = k_1 v^{(s+p)}_{n-j+p} + k_2 v^{(s+p)}_{n-j}$ for every $n \ge j$.

The paper's second clause, $v^{(j)}_n = k_2 v^{(s+p)}_{n+j}$ for $1 \le j \le p$, is omitted: it
fails for $k_1 = k_2 = 1$, $p = 1$, $s = 2$, $j = 1$, $n = 0$, where $v^{(1)}_0 = 1$ but
$v^{(3)}_1 = 0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 2 (`integers-2024-A49-prop-2`). -/
public theorem padovanPerrinFundamental_eq_shift {R : Type*} [CommRing R] (k₁ k₂ : R) (p s j : ℕ)
    (hp : 0 < p) (hpj : p + 1 ≤ j) (hjs : j ≤ s + p - 1) :
    (∀ n, padovanPerrinFundamental k₁ k₂ p s j n =
        padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j)) ∧
      ∀ n, j ≤ n → padovanPerrinFundamental k₁ k₂ p s j n =
        k₁ * padovanPerrinFundamental k₁ k₂ p s (s + p) (n - j + p) +
          k₂ * padovanPerrinFundamental k₁ k₂ p s (s + p) (n - j) := by
  have hs : 0 < s := by omega
  set d : ℕ := s + p - j with hd
  have hshift : ∀ n : ℕ, n + (s + p) - j = n + d := fun n => by omega
  have hwr : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution
      (fun n => padovanPerrinFundamental k₁ k₂ p s (s + p) (n + d)) :=
    padovanPerrin_isSolution_shift _ _
      (padovanPerrinFundamental_isSolution k₁ k₂ p s (s + p)) d
  have hvj : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution
      (padovanPerrinFundamental k₁ k₂ p s j) :=
    padovanPerrinFundamental_isSolution k₁ k₂ p s j
  have heq : padovanPerrinFundamental k₁ k₂ p s j =
      (fun n => padovanPerrinFundamental k₁ k₂ p s (s + p) (n + d)) := by
    apply ((padovanPerrinRecurrence k₁ k₂ p s).eq_iff_eqOn_range_order _ _ hvj hwr).2
    intro m hm
    have hm_lt : m < s + p := Finset.mem_range.mp hm
    dsimp only
    rw [padovanPerrinFundamental_of_lt _ _ _ _ _ _ hm_lt]
    by_cases hmj : m + 1 = j
    · have hmd : m + d = s + p - 1 := by omega
      have hlt : m + d < s + p := by omega
      rw [padovanPerrinFundamental_of_lt _ _ _ _ _ _ hlt, hmd]
      have h1 : s + p - 1 + 1 = s + p := by omega
      simp [hmj, h1]
    · by_cases hmlt : m < j
      · have hlt : m + d < s + p := by omega
        rw [padovanPerrinFundamental_of_lt _ _ _ _ _ _ hlt]
        simp only [hmj, ↓reduceIte]
        have hne : ¬ (m + d + 1 = s + p) := by omega
        simp [hne]
      · have hmt : m + d = (m - j) + (s + p) := by omega
        have hrec := (padovanPerrinRecurrence_isSolution_iff k₁ k₂ p s hs
          (padovanPerrinFundamental k₁ k₂ p s (s + p))).mp
          (padovanPerrinFundamental_isSolution k₁ k₂ p s (s + p)) (m - j)
        rw [hmt, hrec]
        have ht_lt : m - j < s + p := by omega
        have htp_lt : m - j + p < s + p := by omega
        have ht_ne : ¬ (m - j + 1 = s + p) := by omega
        have htp_ne : ¬ (m - j + p + 1 = s + p) := by omega
        rw [padovanPerrinFundamental_of_lt _ _ _ _ _ _ ht_lt,
          padovanPerrinFundamental_of_lt _ _ _ _ _ _ htp_lt]
        simp only [ht_ne, htp_ne, ↓reduceIte, mul_zero, add_zero]
        simp [hmj]
  have hfirst : ∀ n, padovanPerrinFundamental k₁ k₂ p s j n =
      padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j) := by
    intro n
    rw [hshift n]
    exact congrFun heq n
  refine ⟨hfirst, fun n hn => ?_⟩
  rw [hfirst n]
  have hnij : n + (s + p) - j = (n - j) + (s + p) := by omega
  have hrec := (padovanPerrinRecurrence_isSolution_iff k₁ k₂ p s hs
    (padovanPerrinFundamental k₁ k₂ p s (s + p))).mp
    (padovanPerrinFundamental_isSolution k₁ k₂ p s (s + p)) (n - j)
  rw [hnij, hrec]

end MetaMathlibExt
