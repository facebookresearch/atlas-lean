/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Commutator length in `Aut F_n` (Kourovka Notebook Problem 14.15)

Kourovka Notebook, Problem 14.15 (V. G. Bardakov): for `A_n = Aut F_n`, `n ≥ 3`, find the supremum
`k_n` of the commutator lengths of the elements of `A_n'`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AutFreeGroupCommutatorLengthKourovka14Problem15Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.15 (V. G. Bardakov). UnsolvedMath record
UM-00701000 (`KOU-14.15`), dataset ulamai/UnsolvedMath v1.8.0.

The answer `k_n = ∞` is stated as: for every `n ≥ 3` and every `k`, some element of the derived
subgroup of `Aut F_n` is not a product of `k` commutators `x y x⁻¹ y⁻¹`.
-/

/-- **Products of at most $n$ commutators (Kourovka 14.15).** Let $G$ be a group and $n$ a natural
number. An element $z \in G$ is a product of at most $n$ commutators when there are $m \le n$ and
elements $x_1, y_1, \dots, x_m, y_m \in G$ with $z = [x_1, y_1] \cdots [x_m, y_m]$, where
$[x, y] = xyx^{-1}y^{-1}$; for $m = 0$ the empty product is the identity. -/
def IsProductOfCommutators {G : Type*} [Group G] (n : ℕ) (z : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ n ∧ (l.map fun p => p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod = z

/-- **Unbounded commutator length in Aut(Fₙ) (Kourovka 14.15).** The proposition that for every
$n \ge 3$, writing $F_n$ for the free group on $n$ generators, and for every natural number $k$,
some element of the derived subgroup of $\operatorname{Aut}(F_n)$ is not a product of at most $k$
commutators $xyx^{-1}y^{-1}$ of elements of $\operatorname{Aut}(F_n)$. This is the answer
$k_n = \infty$ to Bardakov's question, which asks for the supremum $k_n$ of the commutator lengths
of the elements of the derived subgroup of $\operatorname{Aut}(F_n)$. -/
def autFreeGroupCommutatorLengthUnbounded : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ k : ℕ, ∃ z ∈ commutator (MulAut (FreeGroup (Fin n))),
    ¬ IsProductOfCommutators k z

/--
**Commutator length in Aut(Fₙ) is unbounded.** Let $n \ge 3$ and let $F_n$ be the free group on
$n$ generators. For every natural number $k$ there is an element of the derived subgroup of
$\operatorname{Aut}(F_n)$ that is not a product of at most $k$ commutators $xyx^{-1}y^{-1}$ with
$x, y \in \operatorname{Aut}(F_n)$. Equivalently, the supremum $k_n$ of the commutator lengths of
the elements of the derived subgroup of $\operatorname{Aut}(F_n)$ is infinite.

This answers Kourovka Problem 14.15 (V. G. Bardakov): $\operatorname{Aut}(F_n)$ is acylindrically
hyperbolic (Genevois–Horbez), and acylindrically hyperbolic groups have infinite commutator width
(Bestvina–Bromberg–Fujiwara).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.15 (V. G. Bardakov); resolution: A.
Genevois and C. Horbez, J. Topology 14 (2021), 963-991 (Aut F_n is acylindrically hyperbolic); M.
Bestvina, K. Bromberg and K. Fujiwara, Algebr. Geom. Topol. 19 (2019), 477-489 (acylindrically
hyperbolic groups have infinite commutator width), the Kourovka Notebook (21st issue) marks 14.15
solved: k_n = ∞ for n ≥ 3.
-/
public theorem_wanted autFreeGroupCommutatorLengthUnbounded_holds :
    autFreeGroupCommutatorLengthUnbounded

end MathlibExt.GroupTheory.AutFreeGroupCommutatorLengthKourovka14Problem15Wanted
