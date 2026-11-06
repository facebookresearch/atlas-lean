/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

namespace MetaMathlibExt

@[expose] public section

private lemma U_two {R : Type*} [CommRing R] (c₁ c₂ : R) (U : ℕ → R)
    (hU : ∀ n, U (n + 2) = c₁ * U (n + 1) + c₂ * U n)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1) : U 2 = c₁ := by
  have h := hU 0
  simpa [hU0, hU1] using h

-- Addition formula: any solution shifts via the fundamental solution U.
private lemma shift_eq {R : Type*} [CommRing R] (c₁ c₂ : R) (Z U : ℕ → R)
    (hZ : ∀ n, Z (n + 2) = c₁ * Z (n + 1) + c₂ * Z n)
    (hU : ∀ n, U (n + 2) = c₁ * U (n + 1) + c₂ * U n)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1) :
    ∀ i s, Z (s + (i + 1)) = U (i + 1) * Z (s + 1) + c₂ * U i * Z s := by
  have hU2 : U 2 = c₁ := U_two c₁ c₂ U hU hU0 hU1
  have key : ∀ i, (∀ s, Z (s + (i + 1)) = U (i + 1) * Z (s + 1) + c₂ * U i * Z s) ∧
      (∀ s, Z (s + (i + 2)) = U (i + 2) * Z (s + 1) + c₂ * U (i + 1) * Z s) := by
    intro i
    induction i with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro s
        show Z (s + 1) = U 1 * Z (s + 1) + c₂ * U 0 * Z s
        rw [hU1, hU0]
        ring
      · intro s
        show Z (s + 2) = U 2 * Z (s + 1) + c₂ * U 1 * Z s
        rw [hZ s, hU2, hU1]
        ring
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      intro s
      have hZs := hZ (s + i + 1)
      have hUs1 := hU (i + 1)
      have hUs0 := hU i
      have a1 := ih.2 s
      have a2 := ih.1 s
      have e1 : s + ((i + 1) + 2) = (s + i + 1) + 2 := by ring
      have e2 : (s + i + 1) + 1 = s + (i + 1 + 1) := by ring
      have e3 : s + (i + 1) = s + i + 1 := by ring
      have u3 : i + 2 = (i + 1) + 1 := by ring
      rw [e1, hZs, e2]
      rw [e3] at a2
      rw [u3] at hUs0
      linear_combination c₁ * a1 + c₂ * a2 - Z (s + 1) * hUs1 - (c₂ * Z s) * hUs0
  intro i
  exact (key i).1

-- Casorati determinant scales by (-c₂)^s.
private lemma casorati_eq {R : Type*} [CommRing R] (c₁ c₂ : R) (W Y : ℕ → R)
    (hW : ∀ n, W (n + 2) = c₁ * W (n + 1) + c₂ * W n)
    (hY : ∀ n, Y (n + 2) = c₁ * Y (n + 1) + c₂ * Y n) (j : ℕ) :
    ∀ s, W (s + 1) * Y (s + j) - W s * Y (s + j + 1) =
      (-c₂) ^ s * (W 1 * Y j - W 0 * Y (j + 1)) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    have hWs := hW s
    have hYs := hY (s + j)
    have e1 : s + 1 + 1 = s + 2 := by ring
    have e2 : s + 1 + j = s + j + 1 := by ring
    have e3 : s + j + 1 + 1 = (s + j) + 2 := by ring
    rw [e1, e2, e3, hWs, hYs]
    linear_combination (-c₂) * ih

/-- **Generalized Catalan identity for Horadam sequences.** Let $R$ be a commutative ring, let
$c_1, c_2 \in R$, and let $W, Y, U : \mathbb{N} \to R$ be sequences that each satisfy
$x_{n+2} = c_1 x_{n+1} + c_2 x_n$ for every $n \in \mathbb{N}$, with $U_0 = 0$ and $U_1 = 1$.
Then for all $s, i, j \in \mathbb{N}$,
$$W_{s+i}\,Y_{s+j} - W_s\,Y_{s+i+j} = (-c_2)^s\,(W_1 Y_j - W_0 Y_{j+1})\,U_i.$$

The source states the identity over the integers, with integer coefficients, all integer
indices and $c_2 \ne 0$. This version restricts the indices to natural numbers and allows
coefficients in any commutative ring, so no invertibility of $c_2$ is needed; the bi-infinite
version is not claimed.

Source: Aram Tangboonduangjit and Thotsaporn Thanatipanonda, "Determinants Containing Powers of
Generalized Fibonacci Numbers," Journal of Integer Sequences 19 (2016), Article 16.7.1,
Proposition "Generalized Catalan Identity," lines 111–126 of
`https://cs.uwaterloo.ca/journals/JIS/VOL19/Tangboonduangjit/aram5.tex`.
Proves `Wanted` entry `horadam_generalized_catalan_identity`.
-/
theorem horadam_generalized_catalan_identity
    {R : Type*} [CommRing R] (c₁ c₂ : R) (W Y U : ℕ → R)
    (hW : ∀ n, W (n + 2) = c₁ * W (n + 1) + c₂ * W n)
    (hY : ∀ n, Y (n + 2) = c₁ * Y (n + 1) + c₂ * Y n)
    (hU : ∀ n, U (n + 2) = c₁ * U (n + 1) + c₂ * U n)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1) (s i j : ℕ) :
    W (s + i) * Y (s + j) - W s * Y (s + i + j) =
      (-c₂) ^ s * (W 1 * Y j - W 0 * Y (j + 1)) * U i := by
  cases i with
  | zero => simp [hU0]
  | succ i =>
    have hWs := shift_eq c₁ c₂ W U hW hU hU0 hU1 i s
    have hYs := shift_eq c₁ c₂ Y U hY hU hU0 hU1 i (s + j)
    have hC := casorati_eq c₁ c₂ W Y hW hY j s
    have eY : s + (i + 1) + j = (s + j) + (i + 1) := by ring
    rw [eY, hWs, hYs]
    linear_combination U (i + 1) * hC

end

end MetaMathlibExt
