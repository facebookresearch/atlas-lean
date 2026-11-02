/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular integers modulo `n`: Morgado's characterization

Statements from Klaus Dohmen and Mandy Lange-Geisler, "On the Number of
Regular Integers Modulo `n` and Its Significance for Cryptography",
*Journal of Integer Sequences* 29 (2026), Article 26.2.4
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dohmen/dohmen4.tex>),
Proposition [Morgado 1972] (label `sec:regul-numb-unit-2`, TeX lines
167-176). Definitions are taken from the publisher TeX: an integer `m`
is *regular modulo `n`* if the congruence `m^2 x ≡ m (mod n)` has a
solution `x ∈ ℤ` (Definition [Morgado 1972], TeX lines 108-112), and
`d` is a *unitary divisor* of `n` if `d ∣ n` and `gcd(d, n/d) = 1`
(TeX lines 122-124).

The paper's counting theorem `ϱ(n) = ∑_{d udiv n} φ(d)` (Theorem
[Morgado 1972], equation `eq:2`) is already proved in MathlibExt as
`MetaMathlibExt.morgado_card_regular_modulo`, and its helper chain
proves the leg (a) ↔ (c) of the proposition over `ZMod n`. What is
stated here is the source-shaped three-way equivalence over `ℤ`,
including leg (b) `gcd(m^2, n) = gcd(m, n)`, which is not stated
anywhere else in the repository. The gcds are the paper's
nonnegative gcds, i.e. `Nat.gcd` of `Int.natAbs`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.GCD.Basic

@[expose] public section

/-- **Morgado's characterization of regular integers.** Let $n$ be a positive integer and $m$
an integer, and write $\gcd$ for the nonnegative greatest common divisor. The congruence
$m^2 x \equiv m \pmod{n}$ has a solution $x \in \mathbb{Z}$ if and only if
$\gcd(m^2, n) = \gcd(m, n)$, and $\gcd(m^2, n) = \gcd(m, n)$ holds if and only if $\gcd(m, n)$
and $n / \gcd(m, n)$ are coprime, that is, $\gcd(m, n)$ is a unitary divisor of $n$.

Source: Klaus Dohmen and Mandy Lange-Geisler, "On the Number of
Regular Integers Modulo `n` and Its Significance for Cryptography",
Journal of Integer Sequences 29 (2026), Article 26.2.4, Proposition
[Morgado 1972] (label `sec:regul-numb-unit-2`):
<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dohmen/dohmen4.tex>. -/
theorem_wanted isRegularMod_iff_gcd_sq_eq_gcd {n : ℕ} (hn : 0 < n) (m : ℤ) :
    ((∃ x : ℤ, m ^ 2 * x ≡ m [ZMOD (n : ℤ)])
      ↔ Nat.gcd (m.natAbs ^ 2) n = Nat.gcd m.natAbs n)
    ∧ (Nat.gcd (m.natAbs ^ 2) n = Nat.gcd m.natAbs n
      ↔ Nat.Coprime (Nat.gcd m.natAbs n) (n / Nat.gcd m.natAbs n))
