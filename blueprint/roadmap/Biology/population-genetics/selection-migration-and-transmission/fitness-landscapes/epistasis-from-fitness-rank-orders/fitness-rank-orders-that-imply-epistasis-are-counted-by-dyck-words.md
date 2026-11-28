# Fitness rank orders that imply epistasis are counted by Dyck words

**Setting.** A biallelic $n$-locus system has $2^n$ genotypes $g \in \{0, 1\}^n$ with fitnesses $w_g$. A
landscape is **additive** if $w_g = c_0 + \sum_k c_k g_k$. The **total $n$-way epistasis** is the
interaction coordinate

$$u_{1 \dots 1} = \sum_{g \in \{0,1\}^n} (-1)^{g_1 + \dots + g_n} w_g,$$

for example $u_{11} = w_{00} - w_{10} - w_{01} + w_{11}$; more generally an **additive dependence
relation** is a linear form in the $w_g$ that vanishes on every additive landscape (interaction
coordinates, Walsh coefficients and circuits are examples). A **rank order** is a strict total order of
the $2^n$ fitness values, the only information available in many comparative fitness experiments. A
rank order **implies** $f \ne 0$ if $f \ne 0$ for every landscape compatible with it.

**Word map.** Let $f$ be a nonzero linear form (not all coefficients $0$) with integer coefficients summing to zero. Map a rank order (highest fitness
first) to a word in $\{P, N\}$ by replacing each variable with coefficient $c > 0$ by $P^{c}$, each with
coefficient $c < 0$ by $N^{|c|}$, and deleting variables with coefficient $0$. The zero form must be excluded: its word is empty,
hence trivially Dyck, yet $f = 0$ on every landscape. A **Dyck word** is a word
with equally many $P$ and $N$ in which no prefix has more $N$ than $P$.

**Theorem.** For such a nonzero $f$, a rank order implies $f \ne 0$ if and only if its word, or the word with $P$ and $N$
exchanged, is a Dyck word; in the first case $f > 0$ on every compatible landscape.

**Corollary (counting).** Exactly

$$(2^n)! \cdot \frac{2}{2^{n-1} + 1}$$

rank orders imply total $n$-way epistasis, half of them positive and half negative: 16 for $n = 2$ and
16,128 for $n = 3$. The fraction of all rank orders that imply it is $2 / (2^{n-1} + 1)$, decaying like
$2^{2-n}$. The check is linear in the number of genotypes.

**Further consequences.** For three loci no rank order determines the shape of the landscape (its
triangulation of the 3-cube, one of 74, which is fixed by the sign pattern of the 20 circuits, not by the signs of
the interaction coordinates), and for any $n$, total $n$-way epistasis is implied whenever the
fitness values can be paired as (even genotype, odd genotype) with the even one fitter in every pair.

## Depends on

- [Reciprocal sign epistasis, multiple peaks and the small-face limitation](../epistasis-and-landscape-structure.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

For $u_{1 \dots 1}$ the positive variables are the genotypes with an even number of 1s ($e_1 > e_2 > \dots$)
and the negative ones the odd genotypes ($o_1 > o_2 > \dots$), so $u_{1 \dots 1} = \sum_i (e_i - o_i)$. If the
word is Dyck, each $o_i$ is preceded by $e_i$, so every term is positive. If some prefix first has more
$o$s than $e$s, at $o_j$ with $e_j$ still to come, make $e_j - o_j$ hugely negative and all later values
tiny to get a negative sum. Counting: there are $C_{2^{n-1}}$ Dyck words with $2^{n-1}$ letters of each
kind, each realized by $(2^{n-1})!^2$ rank orders, and doubling for the mirrored sign, which simplifies
with the Catalan formula to the stated count. General forms repeat the argument with letters weighted
by coefficients.

## Sources

- K. Crona, A. Gavryushkin, D. Greene, N. Beerenwinkel, "Inferring genetic interactions from
  comparative fitness data", eLife 6 (2017) e28629, Appendix, Proposition 1, Corollary 2, Definition 1,
  Theorem 3 and Propositions 5 and 7, <https://doi.org/10.7554/elife.28629> (PMC5737811).
