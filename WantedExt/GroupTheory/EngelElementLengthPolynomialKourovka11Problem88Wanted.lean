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

/-- **Commutator for Engel lengths.** For elements $x$ and $y$ of a group, the commutator is
$[x, y] = x^{-1} y^{-1} x y$ (the convention of the Kourovka Notebook). -/
def kcomm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- **Iterated commutators for Engel lengths.** For elements $h$ and $g$ of a group and a natural
number $l$, the iterated commutator $[h, g; l]$ is defined by $[h, g; 0] = h$ and
$[h, g; l + 1] = [[h, g; l], g]$, where $[x, y] = x^{-1} y^{-1} x y$; in particular
$[h, g; 1] = [h, g]$. -/
def engelComm {G : Type*} [Group G] (h g : G) : ℕ → G
  | 0 => h
  | l + 1 => kcomm (engelComm h g l) g

/-- **Bounded Engel element.** An element $g$ of a group $G$ is an Engel element if there is an
$l \ge 1$ such that $[h, g; l] = 1$ for every $h \in G$, where $[h, g; 0] = h$,
$[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$. -/
def IsEngel {G : Type*} [Group G] (g : G) : Prop :=
  ∃ l : ℕ, 1 ≤ l ∧ ∀ h : G, engelComm h g l = 1

/-- **Engel length.** For an element $g$ of a group $G$, the Engel length $l(g)$ is the least
$k \ge 1$ such that $[h, g; k] = 1$ for every $h \in G$, where $[h, g; 0] = h$,
$[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$. If no such $k$ exists, that
is, if $g$ is not an Engel element, then $l(g) = 0$. -/
noncomputable def engelLength {G : Type*} [Group G] (g : G) : ℕ :=
  sInf {l | 1 ≤ l ∧ ∀ h : G, engelComm h g l = 1}

/-- **Roman'kov's problem on Engel lengths of products (Kourovka 11.88).** The statement that every
group $G$ has a polynomial $\varphi(x, y)$ in two variables with natural-number coefficients such
that $l(uv) \le \varphi(l(u), l(v))$ for all $u, v \in G$ for which $u$, $v$ and $uv$ are Engel
elements. Here $g \in G$ is an Engel element if there is a $k \ge 1$ with $[h, g; k] = 1$ for all
$h \in G$, and its Engel length $l(g)$ is the least such $k$, where $[h, g; 0] = h$,
$[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$.

Natural coefficients lose nothing: on $\mathbb{N}^2$ every real polynomial is bounded by one with
natural coefficients. -/
def engelLengthPolynomialBound : Prop :=
  ∀ (G : Type) [Group G], ∃ φ : MvPolynomial (Fin 2) ℕ, ∀ u v : G, IsEngel u → IsEngel v →
    IsEngel (u * v) → engelLength (u * v) ≤ MvPolynomial.eval ![engelLength u, engelLength v] φ

/--
**Engel lengths of products admit no polynomial bound (Kourovka 11.88).** There is a group $G$
such that for every polynomial $\varphi(x, y)$ in two variables with natural-number coefficients
there are $u, v \in G$ such that $u$, $v$ and $uv$ are Engel elements and
$l(uv) > \varphi(l(u), l(v))$. Here $g \in G$ is an Engel element if there is a $k \ge 1$ with
$[h, g; k] = 1$ for all $h \in G$, and its Engel length $l(g)$ is the least such $k$, where
$[h, g; 0] = h$, $[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$.

For a prime $p$, Dolbak builds finite $p$-groups $G_n$ (wreath products of a cyclic group of
order $p$ by groups $K_n$) with elements $c_n$ and $c_n^{-1} b_0$ of Engel length at most
$(n + 1)p - n + 1$ whose product $b_0$ has Engel length at least $p^n$. He takes the direct
product of the $G_n$ in the restricted sense (the direct sum, whose elements have finite support).
It is a single Engel group: an element of finite support has Engel length at most the largest
Engel length of its coordinates, and each $G_n$ is a finite $p$-group, hence nilpotent. (The
unrestricted product is not Engel: the element with $b_0$ in every coordinate has unbounded Engel
length.) Let $u_n$ and $v_n$ be $c_n$ and $c_n^{-1} b_0$ in coordinate $n$ and $1$ elsewhere: they
are Engel elements of length at most $(n + 1)p - n + 1$, and $u_n v_n$ has length at least $p^n$,
which exceeds every polynomial in the lengths of the factors (Theorem 1: there are Engel groups in
which the Engel length of a product of two elements is bounded by no polynomial in the Engel
lengths of the factors). The refutation of this statement uses only that $u_n$, $v_n$ and
$u_n v_n$ are Engel elements of one group. The Kourovka Archive answers 11.88 "No, it does not".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.88 (V. A.
Roman'kov); resolution: L. V. Dolbak, The Engel length of the product of Engel elements, Siberian
Math. J. 47, no. 1 (2006), 55-57, Theorem 1 and its proof; Kourovka Archive, Problem 11.88: "No,
it does not", https://doi.org/10.1007/s11202-006-0006-9.
-/
public theorem_wanted engelLengthPolynomialBound_refuted : ¬ engelLengthPolynomialBound

end MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted
