/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CoveringSystem

namespace Int

@[expose] public section

/-!
# Exact covers by residue classes

Source: Y. Movshovich, *Raabe's Identity and Covering Systems*, Journal of Integer Sequences
23 (2020),
[`movsho5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL23/Movshovich/movsho5.tex).

The definitions extend the repository's indexed covering-system API. In particular, coverage
multiplicity is counted by indices, rather than after converting the family to a `Finset` and
thereby losing repeated residue classes.
-/

/-- **Multiplicity of an indexed system of residue classes.** Given $k \in \mathbb{N}$, moduli
$m_0, \dots, m_{k-1} \in \mathbb{N}$ and residues $r_0, \dots, r_{k-1} \in \mathbb{Z}$, the
multiplicity of an integer $z$ is the number of indices $i < k$ with $z \equiv r_i \pmod{m_i}$.

Indices are counted separately, so a residue class listed several times is counted that many
times; a modulus $m_i = 0$ makes the condition $z = r_i$. -/
public def indexedCoverMultiplicity {k : ℕ} (moduli : Fin k → ℕ)
    (residues : Fin k → ℤ) (z : ℤ) : ℕ :=
  (Finset.univ.filter fun i => z ≡ residues i [ZMOD (moduli i : ℤ)]).card

/-- **Exact covers by residue classes.** Let $k \in \mathbb{N}$, let
$m_0, \dots, m_{k-1} \in \mathbb{N}$ be moduli and $r_0, \dots, r_{k-1} \in \mathbb{Z}$ residues,
and let $M \in \mathbb{N}$ and $T \subseteq \mathbb{Z}$. The system of residue classes
$r_i \bmod m_i$ is an exact $M$-cover of $T$ when $k \ge 2$, every $m_i$ is positive, every
$z \in T$ satisfies $z \equiv r_i \pmod{m_i}$ for exactly $M$ indices $i < k$, and every integer
$z \notin T$ satisfies $z \equiv r_i \pmod{m_i}$ for no index $i < k$.

Indices are counted separately, so a residue class listed several times counts that many times. -/
public def IsExactCoverOf {k : ℕ} (moduli : Fin k → ℕ) (residues : Fin k → ℤ)
    (M : ℕ) (target : Set ℤ) : Prop :=
  2 ≤ k ∧ (∀ i, 0 < moduli i) ∧
    (∀ z, z ∈ target → indexedCoverMultiplicity moduli residues z = M) ∧
    ∀ z, z ∉ target → indexedCoverMultiplicity moduli residues z = 0

end

end Int
