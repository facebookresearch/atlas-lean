# Number of rectangular perturbations of an n-locus system

**Setting.** Consider $n \ge 2$ biallelic loci, genotypes $g \in \{0,1\}^n$ and fitness values $w_g$, of which only the rank order may be known. For a genotype $s$ and a set of loci $S$, write $s^{S}$ for the genotype obtained from $s$ by **replacing** the loci in $S$ ($0 \mapsto 1$, $1 \mapsto 0$).

- A **rectangle** of the $n$-cube is a 4-set $\{s, s^{S_1}, s^{S_2}, s^{S_1 \cup S_2}\}$ with $S_1, S_2$ disjoint and nonempty.
- The system has a **rectangular perturbation of size $k$** if for some rectangle with $|S_1| = k$ the effect of replacing $S_1$ has opposite signs on the two parallel sides:

$$(w_s - w_{s^{S_1}})\,(w_{s^{S_2}} - w_{s^{S_1 \cup S_2}}) < 0 .$$

A size-1 perturbation is exactly **sign epistasis**. Each rectangle has two pairs of parallel sides, so it carries two potential perturbations; it also corresponds to the circuit $w_s + w_{s^{S_1\cup S_2}} - w_{s^{S_1}} - w_{s^{S_2}}$ with four nonzero coefficients, which vanishes for additive fitness.

**Lemma.** For $n \ge 2$ the $n$-cube contains exactly

$$\frac{6^n}{8} - 4^{n-1} + 2^{n-3}$$

rectangles.

**Theorem.** For $n \ge 2$ (stated for $n \ge 3$ in the source) the number of potential rectangular perturbations is

$$2\left(\frac{6^n}{8} - 4^{n-1} + 2^{n-3}\right),$$

and the number of potential perturbations of size $k$ ($1 \le k \le n-1$) is

$$2^{k-1}\binom{n}{k}\binom{2^{n-k}}{2}.$$

**Corollary.** A complete check of sign epistasis in an $n$-locus system requires the signs of $n\binom{2^{n-1}}{2}$ expressions.

For $n = 3$ there are $12$ rectangles and $24$ potential perturbations, $18$ of size 1 and $6$ of size 2; for $n = 4$ there are $100$ rectangles. Among the $8! = 40320$ rank orders of a three-locus system, $384$ show no sign epistasis and, by enumeration, $96$ are compatible with additive fitness. The source notes that for $n \le 4$ a rank order without rectangular perturbations is compatible with additive fitness, while for $n = 5$ the classical counterexamples of Kraft, Pratt and Seidenberg show that this fails.

## Expansion

Rectangles: from a fixed vertex, choose an ordered split of the loci into $S_1, S_2$ (nonempty) and $S_3$ (possibly empty), up to swapping $S_1, S_2$. With $S_3 = \emptyset$ this gives the Stirling number $S(n,2) = 2^{n-1} - 1$ rectangles; with $S_3 \neq \emptyset$ there are three choices of which block is $S_3$, giving $3S(n,3)$ with $S(n,3) = (3^n - 3\cdot 2^n + 3)/6$. Each rectangle has 4 vertices, so the count is $\frac{2^n}{4}\big(3S(n,3) + S(n,2)\big)$, which simplifies to the formula. Each rectangle yields two perturbations, giving the total. For size $k$: choose the $k$ replaced loci ($\binom nk$ ways), an unordered pair {word, complementary word} on them ($2^{k-1}$ ways), and an unordered pair of distinct backgrounds on the other $n-k$ loci ($\binom{2^{n-k}}{2}$ ways). Summing over $k$ recovers the total, e.g. $112 + 72 + 16 = 200$ for $n = 4$; the case $k = 1$ is the corollary.

## Sources

- K. Crona, "Rank orders and signed interactions in evolutionary biology", eLife (2020), Results (definition of rectangular perturbation) and Materials and methods (Theorem 1, Corollary, Lemmas 1 and 2 with proofs; three-locus enumeration), <https://doi.org/10.7554/eLife.51004>, PMCID PMC7000213.
