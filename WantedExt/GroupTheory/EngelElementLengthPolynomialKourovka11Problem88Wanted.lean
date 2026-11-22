/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial bounds for lengths of products of Engel elements (Kourovka Notebook Problem 11.88)

Kourovka Notebook, Archive of Solved Problems, Problem 11.88 (V. A. Roman'kov): the length `l(g)` of
an Engel element `g` is the least `l` with `[h, g; l] = 1` for all `h`. Is there a polynomial
`φ(x, y)` with `l(uv) ≤ φ(l(u), l(v))`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.88 (V. A.
Roman'kov). UnsolvedMath record UM-00700780 (`KOU-11.88`), dataset ulamai/UnsolvedMath v1.8.0.

Engel elements are bounded ones, as in the source and in Dolbak's Definition 1: `[h, g; l] = 1` for
all `h` and some `l ≥ 1`, with `[h, g; 1] = [h, g] = h⁻¹ g⁻¹ h g` and
`[h, g; i + 1] = [[h, g; i], g]`. The polynomial is chosen for each group, as in A. Abdollahi's
survey (Engel elements in groups, arXiv:1002.0309, before Problem 3.27): Roman'kov "asked whether
for any group G there exists a linear (polynomial) function φ(x, y)" with `l(uv) ≤ φ(l(u), l(v))`
for Engel elements `u`, `v` of `G`. The bound is required when `uv` is also Engel, since `l(uv)` is
defined only then; whether products of Engel elements are Engel is left open, as the source notes. A
polynomial serving all groups would serve each group, so the refutation also refutes that reading.
Natural coefficients lose nothing, since on `ℕ²` every real polynomial is bounded by one with
natural coefficients.
-/

/-- The commutator `[x, y] = x⁻¹ y⁻¹ x y` (Kourovka convention). -/
def kcomm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- `[h, g; l]`: `[h, g; 0] = h` and `[h, g; l + 1] = [[h, g; l], g]`, so `[h, g; 1] = [h, g]`. -/
def engelComm {G : Type*} [Group G] (h g : G) : ℕ → G
  | 0 => h
  | l + 1 => kcomm (engelComm h g l) g

/-- `g` is a (bounded) Engel element: `[h, g; l] = 1` for all `h ∈ G`, for some `l ≥ 1`. -/
def IsEngel {G : Type*} [Group G] (g : G) : Prop :=
  ∃ l : ℕ, 1 ≤ l ∧ ∀ h : G, engelComm h g l = 1

/-- The length `l(g)` of an Engel element `g`: the least `l ≥ 1` with `[h, g; l] = 1` for all
`h ∈ G`. -/
noncomputable def engelLength {G : Type*} [Group G] (g : G) : ℕ :=
  sInf {l | 1 ≤ l ∧ ∀ h : G, engelComm h g l = 1}

/-- Kourovka 11.88 (V. A. Roman'kov): every group `G` has a polynomial `φ(x, y)` with
`l(uv) ≤ φ(l(u), l(v))` whenever `u`, `v` and `uv` are Engel elements of `G`. Natural
coefficients lose nothing: on `ℕ²` every real polynomial is bounded by one with natural
coefficients. -/
def engelLengthPolynomialBound : Prop :=
  ∀ (G : Type) [Group G], ∃ φ : MvPolynomial (Fin 2) ℕ, ∀ u v : G, IsEngel u → IsEngel v →
    IsEngel (u * v) → engelLength (u * v) ≤ MvPolynomial.eval ![engelLength u, engelLength v] φ

/--
Resolved false: for a prime `p`, Dolbak builds finite `p`-groups `G_n` (wreath products of a cyclic
group of order `p` by groups `K_n`) with elements `c_n` and `c_n⁻¹ b₀` of Engel length at most
`(n + 1)p - n + 1` whose product `b₀` has Engel length at least `pⁿ`. He takes the direct product of
the `G_n` in the restricted sense (the direct sum, whose elements have finite support). It is a
single Engel group: an element of finite support has Engel length at most the largest Engel length
of its coordinates, and each `G_n` is a finite `p`-group, hence nilpotent. (The unrestricted product
is not Engel: the element with `b₀` in every coordinate has unbounded Engel length.) Let `u_n` and
`v_n` be `c_n` and `c_n⁻¹ b₀` in coordinate `n` and `1` elsewhere: they are Engel elements of length
at most `(n + 1)p - n + 1`, and `u_n v_n` has length at least `pⁿ`, which exceeds every polynomial
in the lengths of the factors (Theorem 1: there are Engel groups in which the Engel length of a
product of two elements is bounded by no polynomial in the Engel lengths of the factors). The
refutation of this statement uses only that `u_n`, `v_n` and `u_n v_n` are Engel elements of one
group. The Kourovka Archive answers 11.88 "No, it does not". Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 11.88 (V. A. Roman'kov); resolution: L. V. Dolbak, The
Engel length of the product of Engel elements, Siberian Math. J. 47, no. 1 (2006), 55-57, Theorem 1
and its proof; Kourovka Archive, Problem 11.88: "No, it does not",
https://doi.org/10.1007/s11202-006-0006-9.
-/
public theorem_wanted engelLengthPolynomialBound_refuted : ¬ engelLengthPolynomialBound

end MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted
