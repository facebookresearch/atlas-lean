/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion

/-!
# Product identity for the Padovan–Perrin fundamental system

The product identity is the entrywise form of multiplying two powers of the companion matrix.
The paper uses one-based indices; the matrix entries use zero-based `Fin` indices.
-/

@[expose] public section

namespace MetaMathlibExt

variable {R : Type*}

/-- **Product identity for the generalized Padovan–Perrin fundamental system.** Let $R$ be a
commutative ring, $k_1, k_2 \in R$, and $p, s \ge 1$. Write $r = s + p$ and $v^{(\ell)}$ for the
$\ell$-th sequence of the Fibonacci fundamental system of the $([k]; p; s)$-Padovan–Perrin
recurrence. Then for all $m, n \ge 0$ and all $1 \le i, j \le r$,

$$v^{(r-j+1)}_{n+m+r-i} = \sum_{k=1}^{r} v^{(r-k+1)}_{m+r-i} \, v^{(r-j+1)}_{n+r-k}.$$

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 3, equation (10) (`integers-2024-A49-prop-3`). -/
public theorem padovanPerrinFundamental_mul_sum [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (m n i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ s + p) (hj : 1 ≤ j)
    (hj' : j ≤ s + p) :
    padovanPerrinFundamental k₁ k₂ p s (s + p - j + 1) (n + m + (s + p) - i) =
      ∑ k ∈ Finset.Icc 1 (s + p),
        padovanPerrinFundamental k₁ k₂ p s (s + p - k + 1) (m + (s + p) - i) *
          padovanPerrinFundamental k₁ k₂ p s (s + p - j + 1) (n + (s + p) - k) := by
  set r := s + p
  let A : Matrix (Fin r) (Fin r) R := Matrix.of fun a b =>
    if (a : ℕ) = 0 then
      (if (b : ℕ) + 1 = s then k₁ else 0) + (if (b : ℕ) + 1 = r then k₂ else 0)
    else if (a : ℕ) = (b : ℕ) + 1 then 1 else 0
  have entry (t : ℕ) (a b : Fin r) :
      (A ^ t) a b = padovanPerrinFundamental k₁ k₂ p s (r - ((b : ℕ) + 1) + 1)
        (t + r - ((a : ℕ) + 1)) := by
    rw [show r - ((b : ℕ) + 1) + 1 = r - (b : ℕ) by omega,
      show t + r - ((a : ℕ) + 1) = t + r - 1 - (a : ℕ) by omega]
    exact padovanPerrin_companion_pow_apply k₁ k₂ p s hp hs t a b
  let a : Fin r := ⟨i - 1, by omega⟩
  let b : Fin r := ⟨j - 1, by omega⟩
  have ha : (a : ℕ) + 1 = i := by dsimp [a]; omega
  have hb : (b : ℕ) + 1 = j := by dsimp [b]; omega
  calc
    _ = (A ^ (n + m)) a b := by rw [entry, ha, hb]
    _ = ∑ c : Fin r, (A ^ m) a c * (A ^ n) c b := by
      rw [Nat.add_comm n m, pow_add, Matrix.mul_apply]
    _ = _ := by
      simp only [entry, ha, hb]
      refine Finset.sum_bij (fun c _ => (c : ℕ) + 1) ?_ ?_ ?_ ?_
      · intro c _
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro c _ d _ h
        exact Fin.ext (by omega)
      · intro k hk
        obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
        exact ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
      · intros
        rfl

end MetaMathlibExt
