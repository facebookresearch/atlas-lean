/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.TracesOfIrreducibleQuadratics
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# A $p$-adic integer trace with residue in $U_p$ gives an irreducible quadratic

For a prime $p$ and $s \in \mathbb{Z}_p$ whose residue $\operatorname{red}_p(s) \in \mathbb{F}_p$
lies in $U_p$, the set of $t \in \mathbb{F}_p$ with $x^2 - tx + 1$ irreducible over $\mathbb{F}_p$
(`FiniteField.tracesOfIrreducibleQuadratics`), the polynomial $x^2 - sx + 1$ is irreducible over
$\mathbb{Q}_p$.

This is a step of the proof of Lemma 2.1(ii) of B. Poonen, "Characterizing integers among rational
numbers with a universal-existential formula", Amer. J. Math. 131 (2009), 675–682.
-/

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace Padic

/-- **A $p$-adic integer trace with residue in $U_p$ gives an irreducible quadratic.** Let $p$ be a
prime and let $s \in \mathbb{Z}_p$. If the residue $\operatorname{red}_p(s) \in \mathbb{F}_p$
(`PadicInt.toZMod`) lies in $U_p$, that is, $x^2 - \operatorname{red}_p(s)\, x + 1$ is irreducible
in $\mathbb{F}_p[x]$, then $x^2 - sx + 1$ is irreducible in $\mathbb{Q}_p[x]$.

The proof: a root $r \in \mathbb{Q}_p$ of $x^2 - sx + 1$ would satisfy
$\lVert r \rVert^2 = \lVert sr - 1 \rVert \le \max(\lVert r \rVert, 1)$, so $\lVert r \rVert \le 1$
and $r \in \mathbb{Z}_p$; then $\operatorname{red}_p(r)$ would be a root of
$x^2 - \operatorname{red}_p(s)\, x + 1$ in $\mathbb{F}_p$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.1(ii), p. 3 of the author's version
with the corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "If
$\operatorname{red}_p(s) \in U_p$, then $x^2 - sx + 1$ is irreducible over $\mathbb{Q}_p$", with
$\operatorname{red}_p \colon \mathbb{Z}_p \to \mathbb{F}_p$ the reduction map and $U_p$ as in §2,
p. 2. -/
theorem irreducible_X_sq_sub_C_mul_X_add_one_of_toZMod_mem {p : ℕ} [Fact p.Prime] {s : ℤ_[p]}
    (hs : PadicInt.toZMod s ∈ FiniteField.tracesOfIrreducibleQuadratics (ZMod p)) :
    Irreducible (X ^ 2 - C (s : ℚ_[p]) * X + 1 : ℚ_[p][X]) := by
  change (s : ℚ_[p]) ∈ FiniteField.tracesOfIrreducibleQuadratics ℚ_[p]
  rw [FiniteField.mem_tracesOfIrreducibleQuadratics_iff] at hs ⊢
  intro r hr
  have hs1 : ‖(s : ℚ_[p])‖ ≤ 1 := s.norm_le_one
  have hr1 : ‖r‖ ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : r ^ 2 = s * r + -1 := by linear_combination hr
    have hle : ‖r‖ ^ 2 ≤ max (‖(s : ℚ_[p])‖ * ‖r‖) 1 := by
      rw [← norm_pow, h2, ← norm_mul, ← norm_one (α := ℚ_[p]), ← norm_neg (1 : ℚ_[p])]
      exact Padic.nonarchimedean _ _
    have hsr : ‖(s : ℚ_[p])‖ * ‖r‖ ≤ ‖r‖ := by nlinarith [norm_nonneg r]
    have hmax : max (‖(s : ℚ_[p])‖ * ‖r‖) 1 ≤ ‖r‖ := max_le hsr h.le
    nlinarith
  set r' : ℤ_[p] := ⟨r, hr1⟩ with hr'def
  have hr' : r' ^ 2 - s * r' + 1 = 0 := by
    have h : ((r' ^ 2 - s * r' + 1 : ℤ_[p]) : ℚ_[p]) = 0 := by
      push_cast
      exact hr
    exact Subtype.ext h
  apply hs (PadicInt.toZMod r')
  simpa using congrArg PadicInt.toZMod hr'

end Padic
