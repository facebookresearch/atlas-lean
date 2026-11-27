/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Leonardo `p`-numbers and Lucas-Leonardo `p`-numbers: tilings, incomplete and hyper analogs

Statements from Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo
`p`-Numbers and Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57
(<https://math.colgate.edu/~integers/z57/z57.pdf>).

The Leonardo `p`-numbers `𝓛_{p,n}` (`1` on `[0, p]`, `𝓛_{p,n} = 𝓛_{p,n-1} + 𝓛_{p,n-p-1} + p`)
are the generalized Leonardo `p`-numbers `leonardoPK p p` of
`WantedExt.NumberTheory.LeonardoPWanted`. Propositions 3, 4 and 5 of the paper are the
`k = p` cases of `leonardoPK_eq`, `sum_leonardoPK` and `sum_leonardoPK_stride` there, and
are not restated. The theorem `card_leonardoPTilings` is proved in
`MathlibExt.NumberTheory.LeonardoPTilingsCardLeonardoPTilings`, and is not restated.

The tiling and sequence definitions in `MathlibExt.NumberTheory.LeonardoPTilings` include the
Lucas `p`-numbers `lucasP`, the Lucas-Leonardo `p`-numbers `lucasLeonardoP`,
the incomplete Lucas-Leonardo `p`-numbers (the paper's
display (8)), the hyper Leonardo `p`-numbers (display (12)), the hyper
Lucas-Leonardo `p`-numbers (Definition 2), the tiling sets `K_{p,n}` and the bracelet sets
`B_{p,n}`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.NumberTheory.IncompleteLeonardoP
public import MathlibExt.NumberTheory.IncompleteLeonardoPBinomialSum
public import MathlibExt.NumberTheory.IncompleteLeonardoPPartialSum
public import MathlibExt.NumberTheory.HyperLeonardoPRec
public import MathlibExt.NumberTheory.LeonardoPTilings
public import MathlibExt.NumberTheory.LucasLeonardoPIdentity
public import MathlibExt.NumberTheory.LucasLeonardoPPrefixSum
public import MathlibExt.NumberTheory.LucasLeonardoPStrideSum
public import WantedExt.NumberTheory.LeonardoPWanted
public import MathlibExt.NumberTheory.LeonardoPTilingsCardLeonardoPTilings

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.LeonardoPWanted

/-- **Homogeneous recurrence for the Leonardo $p$-numbers.** Let $p \ge 1$ and write
$\mathcal{L}_{p,n}$ for the Leonardo $p$-number $\mathcal{L}_{p,p}(n)$, the generalized Leonardo
$p$-number with $k = p$. Then $\mathcal{L}_{p,n} = \mathcal{L}_{p,n-1} + \mathcal{L}_{p,n-p} -
\mathcal{L}_{p,n-2p-1}$ for every $n \ge 2p + 1$, $\mathcal{L}_{p,i} = 1$ for every $i \le p$,
and $\mathcal{L}_{p,p+j} = (j + 1) + jp$ for every $j$ with $1 \le j \le p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 2. -/
public theorem_wanted leonardoPK_self_homogeneous (p : ℕ) (hp : 1 ≤ p) :
    (∀ n, 2 * p + 1 ≤ n →
      leonardoPK p p n =
        leonardoPK p p (n - 1) + leonardoPK p p (n - p) - leonardoPK p p (n - 2 * p - 1)) ∧
    (∀ i, i ≤ p → leonardoPK p p i = 1) ∧
    (∀ j, 1 ≤ j → j ≤ p → leonardoPK p p (p + j) = (j : ℤ) + 1 + j * p)

/-- **Leonardo p-numbers split into incomplete and hyper parts.** For natural numbers $p \ge 1$,
$n > p$ and $k \ge 1$, let $N = n + (p + 1)k$. Then
$$
\mathcal{L}_{p,N} = \mathcal{L}_{p,N}(k - 1) + \mathcal{L}^{(k)}_{p,n} + p \binom{n + k}{k},
$$
where $\mathcal{L}_{p,N}$ is the Leonardo $p$-number (the generalized Leonardo $p$-numbers with
additive constant $p$: $\mathcal{L}_{p,m} = 1$ for $m \le p$ and
$\mathcal{L}_{p,m} = \mathcal{L}_{p,m-1} + \mathcal{L}_{p,m-p-1} + p$ for $m > p$),
$\mathcal{L}_{p,N}(k - 1)$ is the incomplete Leonardo $p$-number and $\mathcal{L}^{(k)}_{p,n}$ is
the hyper Leonardo $p$-number.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 11. -/
public theorem_wanted leonardoPK_eq_incomplete_add_hyper (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p < n) (hk : 1 ≤ k) :
    leonardoPK p p (n + (p + 1) * k) =
      incompleteLeonardoP p (n + (p + 1) * k) (k - 1) + hyperLeonardoP p n k +
        p * ((n + k).choose k : ℤ)

/-- **Counting Lucas–Leonardo bracelets.** For all natural numbers $p \ge 1$ and $n \ge 1$, let
$B_{p,n}$ be the set of tilings of a circular $n$-board by curved squares (length $1$), curved
$p$-minos (length $p + 1$) and at most one curved $p$-tile in one of $p$ colors, which if present
is the tile covering cell $1$ and either has length $p + 1$, in any of its $p + 1$ phases, or has
length at least $p + 2$ and starts at cell $1$. Then the number of bracelets in $B_{p,n}$ equals
the Lucas–Leonardo $p$-number $R_{p,n}$, given by $R_{p,0} = p^2 + p + 1$, $R_{p,i} = 1$ for
$1 \le i \le p$ and $R_{p,n} = R_{p,n-1} + R_{p,n-p-1} + p$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 12. -/
public theorem_wanted card_lucasLeonardoBracelets (p n : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (Nat.card (lucasLeonardoBracelets p n) : ℤ) = lucasLeonardoP p n

/-- **Lucas-Leonardo $p$-numbers from Lucas $p$-numbers.** For every $p \ge 1$ and every
natural number $n$, the Lucas-Leonardo $p$-number $R_{p,n}$ and the Lucas $p$-number $L_{p,n}$
satisfy $R_{p,n} = (p + 1) L_{p,n} - p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 13. -/
public theorem_wanted lucasLeonardoP_eq_lucasP (p n : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p n = ((p : ℤ) + 1) * lucasP p n - p

/-- **Recurrence for incomplete Lucas-Leonardo p-numbers.** For natural numbers $p \ge 1$,
$n > p + 1$ and $k \le \lfloor n/(p+1) \rfloor$, the incomplete Lucas-Leonardo $p$-numbers
$R_{p,m}(j)$ satisfy
$$
R_{p,n}(k + 1) = R_{p,n-1}(k + 1) + R_{p,n-p-1}(k) + p.
$$

At $n = p + 1$ the term $R_{p,0}(k)$ would contain the undefined summand
$\frac{0}{0} \binom{0}{0}$, so that case is excluded.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 17. -/
public theorem_wanted incompleteLucasLeonardoP_succ (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p + 1 < n) (hk : k ≤ n / (p + 1)) :
    incompleteLucasLeonardoP p n (k + 1) =
      incompleteLucasLeonardoP p (n - 1) (k + 1) + incompleteLucasLeonardoP p (n - p - 1) k +
        p

/-- **Binomial sum identity for incomplete Lucas-Leonardo p-numbers.** For natural numbers
$p \ge 1$, $n$, $r$ and $k$ with $n \ge p + r$ and $k \le \lfloor (n - p - r)/(p + 1) \rfloor$,
the incomplete Lucas-Leonardo $p$-numbers $R_{p,m}(j)$ satisfy, as rational numbers,
$$
\sum_{i=0}^{r} \binom{r}{i} R_{p,n+pi}(k + i) + (2^r - 1) p = R_{p,n+(p+1)r}(k + r).
$$

The paper prints the range as $0 \le n \le \lfloor (n - p - r)/(p + 1) \rfloor$; the first $n$
is read as $k$, as in Proposition 7.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 18. -/
public theorem_wanted sum_choose_mul_incompleteLucasLeonardoP (p n r k : ℕ) (hp : 1 ≤ p)
    (hnr : p + r ≤ n) (hk : k ≤ (n - p - r) / (p + 1)) :
    ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℚ) * incompleteLucasLeonardoP p (n + p * i) (k + i) +
        ((2 : ℚ) ^ r - 1) * p =
      incompleteLucasLeonardoP p (n + (p + 1) * r) (k + r)

/-- **Hyper Lucas–Leonardo numbers from incomplete ones.** For natural numbers $p \ge 1$, $n > p$
and $k \ge 1$, write $R_{p,m}$ for the Lucas–Leonardo $p$-numbers and $R_{p,m}(j)$ for the
incomplete Lucas–Leonardo $p$-numbers. Then the hyper Lucas–Leonardo $p$-number $R^{(k)}_{p,n}$
satisfies

$$R^{(k)}_{p,n} = R_{p,n+(p+1)k} - R_{p,n+(p+1)k}(k - 1) - p \binom{n + k}{k}.$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 19. -/
public theorem_wanted hyperLucasLeonardoP_eq (p n k : ℕ) (hp : 1 ≤ p) (hn : p < n)
    (hk : 1 ≤ k) :
    hyperLucasLeonardoP p n k =
      lucasLeonardoP p (n + (p + 1) * k) -
        incompleteLucasLeonardoP p (n + (p + 1) * k) (k - 1) - p * ((n + k).choose k : ℚ)

end

end MetaMathlibExt
