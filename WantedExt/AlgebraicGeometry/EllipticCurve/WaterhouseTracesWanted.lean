/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 6 (Waterhouse), as quoted by Vallières, in point-count form: let
`F` be a finite field with `q = p ^ a` elements. An integer `β` is the
Frobenius trace `q + 1 - #E(F)` of some elliptic curve `E` over `F` if and only
if `|β| ≤ 2 √q` (written `β² ≤ 4q`) and one of the following holds:
1. `gcd(β, p) = 1`;
2. `a` is even and `β = ± 2 √q`;
3. `a` is even, `p ≢ 1 (mod 3)` and `β = ± √q`;
4. `a` is odd, `p = 2` or `p = 3`, and `β = ± p ^ ((a + 1) / 2)`;
5. `a` is odd, or `a` is even and `p ≢ 1 (mod 4)`, and `β = 0`.

The paper states a one-to-one correspondence between `F`-isogeny classes and
these `β`; this declaration records which `β` occur (the image of the
correspondence). Injectivity is Tate's isogeny theorem (Corollary 2), which
Mathlib cannot state without isogenies.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan
Graphs on Two Vertices*, INTEGERS 24 (2024), Article A8, Theorem 6
(`integers-2024-A8-thm-6`). -/
public theorem_wanted exists_isElliptic_frobeniusTrace_eq_iff {F : Type*} [Field F]
    [Finite F] {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (hq : Nat.card F = p ^ a) (β : ℤ) :
    (∃ W : WeierstrassCurve F, W.IsElliptic ∧ W.toAffine.frobeniusTrace = β) ↔
      β ^ 2 ≤ 4 * (p : ℤ) ^ a ∧
        (Int.gcd β p = 1 ∨
          (Even a ∧ (β = 2 * (p : ℤ) ^ (a / 2) ∨ β = -(2 * (p : ℤ) ^ (a / 2)))) ∨
          (Even a ∧ ¬ p ≡ 1 [MOD 3] ∧ (β = (p : ℤ) ^ (a / 2) ∨ β = -(p : ℤ) ^ (a / 2))) ∨
          (Odd a ∧ (p = 2 ∨ p = 3) ∧
            (β = (p : ℤ) ^ ((a + 1) / 2) ∨ β = -(p : ℤ) ^ ((a + 1) / 2))) ∨
          ((Odd a ∨ (Even a ∧ ¬ p ≡ 1 [MOD 4])) ∧ β = 0))

/-- Theorem 2 (Ihara, as quoted by Vallières), in adjacency-matrix form. Let `q ≥ 2` and let `A`
be a symmetric integer matrix (the adjacency matrix of a `(q + 1)`-regular graph). The graph is
Ramanujan, i.e. every eigenvalue `μ ≠ q + 1` of `A` satisfies `|μ| ≤ 2 √q`, if and only if every
non-trivial zero of `Q_X(s) = ζ_X(q^{-s})⁻¹`, i.e. every `s` with
`1 - μ q^{-s} + q^{1 - 2s} = 0` for an eigenvalue `μ ≠ q + 1`, lies on `Re s = 1/2`.

The non-trivial zeros are those of `P_X(q^{-s}) = ∏_{μ ≠ q + 1} (1 - μ q^{-s} + q^{1 - 2s})`, as in
the paper. Eigenvalues are the complex roots of the characteristic polynomial (all real, since `A`
is symmetric). The paper's connectedness, regularity and `|V_X| ≥ 2` assumptions are not needed
in this form: the equivalence holds eigenvalue by eigenvalue.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 2 (`integers-2024-A8-thm-2`). -/
public theorem_wanted ramanujan_iff_nontrivial_zeros_re_eq_half {n q : ℕ} (hq : 2 ≤ q)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) :
    (∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ‖μ‖ ≤ 2 * Real.sqrt q) ↔
      ∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ∀ s : ℂ,
        1 - μ * (q : ℂ) ^ (-s) + (q : ℂ) ^ (1 - 2 * s) = 0 → s.re = 1 / 2

/-- Proposition 1 of Vallières, in adjacency-matrix form: let `A` be a symmetric integer matrix
(the adjacency matrix of a `(q + 1)`-regular graph `X`) that is Ramanujan, i.e. every eigenvalue
`μ ≠ q + 1` satisfies `|μ| ≤ 2 √q`. Then every inverse root `α` of
`P_X(u) = ∏_{μ ≠ q + 1} (1 - μ u + q u²)`, i.e. every root of `t² - μ t + q` for an eigenvalue
`μ ≠ q + 1`, is a Weil `q`-number: an algebraic integer all of whose conjugates (the roots in `ℂ`
of its minimal polynomial over `ℚ`, i.e. its images under the embeddings `ℚ(α) → ℂ`) have
absolute value `√q`.

The paper takes `q = p ^ a` and `X` connected; neither is needed here, so `q` is any natural
number and the regularity and connectedness hypotheses are dropped (symmetry keeps the eigenvalues
real). The product formula for `P_X` is the one displayed in the paper (Section 2.1.3).

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Proposition 1 (`integers-2024-A8-prop-1`). -/
public theorem_wanted isWeilNumber_of_ramanujan {n q : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.IsSymm)
    (hram : ∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ‖μ‖ ≤ 2 * Real.sqrt q)
    {μ α : ℂ} (hμ : μ ∈ A.charpoly.aroots ℂ) (hμq : μ ≠ (q : ℂ) + 1)
    (hα : α ^ 2 - μ * α + q = 0) :
    IsIntegral ℤ α ∧ ∀ β ∈ (minpoly ℚ α).aroots ℂ, ‖β‖ = Real.sqrt q

/-- Theorem 8 (Theorem A) of Vallières, in point-count form. Let `F` be a finite field with
`q = p ^ a` elements, `p` an odd prime and `a ∈ {1, 2}`. A natural number `N` is the number of
`F`-points of an elliptic curve over `F` with `4 ∣ N` if and only if `N = 2m` for the two-vertex
graph `X(l, m)` (`m` edges between the vertices, `l` loops at each vertex, `2l + m = q + 1`) that is
connected (`0 < m`) and Ramanujan. The non-trivial eigenvalue of `X(l, m)` is `2l - m`, so the
Ramanujan condition `|2l - m| ≤ 2 √q` is written `(2l - m)² ≤ 4q`.

The paper's map `[C] ↦ X(l, m)` with `m = #C(F)/2` and `l = (q + 1)/2 - #C(F)/4` is a bijection from
`F`-isogeny classes; this declaration states that it is well defined (lands in connected Ramanujan
graphs with `l, m ∈ ℕ`) and surjective, at the level of point counts. Injectivity on isogeny classes
is Tate's theorem (Corollary 2), omitted because Mathlib has no isogenies.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 8 (`integers-2024-A8-thm-8`). -/
public theorem_wanted exists_isElliptic_card_eq_iff_ramanujan_two_vertices {F : Type*} [Field F]
    [Finite F] {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : a = 1 ∨ a = 2)
    (hq : Nat.card F = p ^ a) (N : ℕ) :
    (∃ W : WeierstrassCurve F, W.IsElliptic ∧ Nat.card W.toAffine.Point = N ∧ 4 ∣ N) ↔
      ∃ l m : ℕ, N = 2 * m ∧ 2 * l + m = p ^ a + 1 ∧ 0 < m ∧
        ((2 * l : ℤ) - m) ^ 2 ≤ 4 * (p : ℤ) ^ a

/-- Theorem 9 of Vallières, in point-count form. Let `F` be a finite field with `q = p ^ a`
elements, `p` an odd prime and `a ≥ 1` arbitrary. A natural number `N` is the number of `F`-points
of an ordinary elliptic curve over `F` with `4 ∣ N` if and only if `N = 2m` for a connected
Ramanujan two-vertex graph `X(l, m)` (`2l + m = q + 1`, `0 < m`, `(2l - m)² ≤ 4q`) with
`2m ≢ 1 (mod p)`.

Ordinary is written `gcd(a_q(E), p) = 1` for the Frobenius trace `a_q(E) = q + 1 - #E(F)`, the
criterion the paper uses (an elliptic curve is supersingular iff `p ∣ a_q(E)`). As for Theorem 8,
the isogeny-class bijection is stated at the level of point counts (well defined and surjective);
injectivity (Tate) is omitted.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 9 (`integers-2024-A8-thm-9`). -/
public theorem_wanted exists_ordinary_card_eq_iff_ramanujan_two_vertices {F : Type*} [Field F]
    [Finite F] {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hq : Nat.card F = p ^ a) (N : ℕ) :
    (∃ W : WeierstrassCurve F, W.IsElliptic ∧ Int.gcd W.toAffine.frobeniusTrace p = 1 ∧
        Nat.card W.toAffine.Point = N ∧ 4 ∣ N) ↔
      ∃ l m : ℕ, N = 2 * m ∧ 2 * l + m = p ^ a + 1 ∧ 0 < m ∧
        ((2 * l : ℤ) - m) ^ 2 ≤ 4 * (p : ℤ) ^ a ∧ ¬ 2 * m ≡ 1 [MOD p]

end

end MetaMathlibExt
