/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

/-!
# Divisibility in absolute Lucas pseudoprime constructions
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Ballot's Lemma 3: the three divisibilities persist modulo $c_1 c_2 c_3$.** Let
$\varepsilon_1, \varepsilon_2, \varepsilon_3 \in \{1, -1\}$, let $c_1, c_2, c_3$ be pairwise coprime
positive integers, let $\varepsilon = \varepsilon_1 \varepsilon_2 \varepsilon_3$, and let $g \ne 0$
be an integer such that $c_i g$ divides
$(c_1 g + \varepsilon_1)(c_2 g + \varepsilon_2)(c_3 g + \varepsilon_3) - \varepsilon$ for
$i = 1, 2, 3$. Then every nonzero integer $h \equiv g \pmod{c_1 c_2 c_3}$ satisfies the same
divisibilities: $c_i h$ divides
$(c_1 h + \varepsilon_1)(c_2 h + \varepsilon_2)(c_3 h + \varepsilon_3) - \varepsilon$ for
$i = 1, 2, 3$.

The divisibility hypothesis on $g$ is needed: for $(c_1, c_2, c_3) = (1, 2, 3)$,
$\varepsilon_1 = \varepsilon_2 = \varepsilon_3 = 1$ and $g = h = 1$, the product is $24$ and
$2 \nmid 24 - 1$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 3 (`integers-2026-A102-lem-3`). -/
public theorem mul_dvd_prod_sub_sign_of_modEq {ε₁ ε₂ ε₃ c₁ c₂ c₃ g h : ℤ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (h₁₂ : IsCoprime c₁ c₂) (h₁₃ : IsCoprime c₁ c₃) (h₂₃ : IsCoprime c₂ c₃) (hg : g ≠ 0)
    (hgdvd : ∀ c ∈ ({c₁, c₂, c₃} : Finset ℤ),
      c * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃)
    (hh : h ≠ 0) (hhg : h ≡ g [ZMOD c₁ * c₂ * c₃]) :
    ∀ c ∈ ({c₁, c₂, c₃} : Finset ℤ),
      c * h ∣ (c₁ * h + ε₁) * (c₂ * h + ε₂) * (c₃ * h + ε₃) - ε₁ * ε₂ * ε₃ := by
  let Q (x : ℤ) :=
    c₁ * (c₂ * x + ε₂) * (c₃ * x + ε₃) + ε₁ * c₂ * (c₃ * x + ε₃) + ε₁ * ε₂ * c₃
  have factor (x : ℤ) :
      (c₁ * x + ε₁) * (c₂ * x + ε₂) * (c₃ * x + ε₃) - ε₁ * ε₂ * ε₃ = Q x * x := by
    dsimp [Q]
    ring
  intro c hc
  have hmod : h ≡ g [ZMOD c] := by
    apply hhg.of_dvd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · exact dvd_mul_left _ _
  have hQ : Q h ≡ Q g [ZMOD c] := by
    dsimp [Q]
    gcongr
  have hd := hgdvd c hc
  rw [factor, mul_dvd_mul_iff_right hg] at hd
  rwa [factor, mul_dvd_mul_iff_right hh, hQ.dvd_iff]

end MetaMathlibExt
