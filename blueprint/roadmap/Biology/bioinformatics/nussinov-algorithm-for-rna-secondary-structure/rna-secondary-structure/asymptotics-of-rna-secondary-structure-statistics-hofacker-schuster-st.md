# Asymptotics of RNA secondary structure statistics

Consider abstract RNA secondary structures on $n$ positions $1, \dots, n$ with minimum hairpin loop size $m$ and minimum stack length $1$: noncrossing sets of pairs $(i, j)$ with $j - i > m$ in which each position lies in at most one pair, where every such pair is admissible, independently of any sequence or base-pairing rule, and all structures are counted equally. (Equal weights alone would not suffice: forbidding some separated pairs changes the counts, already for $n = m + 2$, where the only possible pair is $(1, n)$.) Their number is [Waterman's number](../../mccaskill-partition-function-for-rna-folding/card-structures-eq-waterman-number.md) $S_m(n)$, given by [Waterman's recursion](../../mccaskill-partition-function-for-rna-folding/waterman-number.md), and $S_0(n)$ is the [Motzkin number](../../mccaskill-partition-function-for-rna-folding/waterman-number-zero-eq-motzkin-number.md). Hofacker, Schuster and Stadler (1998) show that the generating function $s(x) = \sum_k S_m(k)x^k$ satisfies $1 + (2x - \sum_{k=0}^{m+1}x^k)s + x^2s^2 = 0$ (Corollary 4.10), and derive from it (Corollaries 4.11–4.12, via their Theorem 4.3) the asymptotics $S_m(n) \sim c\,n^{-3/2}\alpha^{-n}$, where $\alpha$ is the smallest positive root of $\sum_{k=0}^{m+1}\alpha^k - 4\alpha = 0$ and the constant $c = -g(\alpha)/(2\sqrt\pi)$ is tabulated in their Table 1; thus $\alpha = (3 - \sqrt5)/2 \approx 0.3820$ for $m = 1$, $\alpha \approx 0.4369$ for $m = 3$, and for $m = 0$, $\alpha = 1/3$ with $c \approx 1.4658 = \sqrt{27/(4\pi)}$. Averaged over all structures, the number of components tends to $2/\alpha - 3$ (Theorem 4.14), the number of external positions tends to $2$ (Theorem 4.16), the number of unpaired positions is $\sim \frac{2\alpha + m(1 - 2\alpha)}{2 + m(1 - 2\alpha)}\,n$ (Theorem 4.17), and the number of stacks is $\sim \frac{(1 - \alpha)^2(1 + \alpha)}{2 + m - 2m\alpha}\,n$ (Theorem 4.19). Since unpaired positions plus twice the base pairs equal $n$ (Remark 4.18), the average number of base pairs is $\sim \frac{1 - \alpha}{2 + m(1 - 2\alpha)}\,n$, about $0.276\,n$ for $m = 1$ and $0.237\,n$ for $m = 3$.

## Depends on

- [Waterman's recursion](../../mccaskill-partition-function-for-rna-folding/waterman-number.md)
- [Number of secondary structures is Waterman's number](../../mccaskill-partition-function-for-rna-folding/card-structures-eq-waterman-number.md)
- [Waterman numbers with no hairpin constraint are Motzkin numbers](../../mccaskill-partition-function-for-rna-folding/waterman-number-zero-eq-motzkin-number.md)

## Expansion

1. Abstract secondary structures as noncrossing matchings with separation greater than $m$ and no sequence constraint, and the functional equation of Corollary 4.10 from Waterman's recursion.
2. The singularity analysis (Theorems 4.2–4.3) giving the growth of $S_m(n)$, equations (47)–(50), and the constants of Table 1.
3. The generating functions marking components, external positions, unpaired positions and stacks (Lemma 4.13, Theorems 4.14–4.19), via the transfer results of Theorems 4.5–4.6.
4. The base-pair density from Remark 4.18, and the special cases $m = 0$ and $m = 1$.
5. Counts with a given number of base pairs, hairpins, components or external positions, and loop and stack length distributions (Theorems 4.20–4.30), and minimum stack lengths greater than $1$, as separate statements.

## Sources

- I. L. Hofacker, P. Schuster and P. F. Stadler, Combinatorics of RNA secondary structures, Discrete Appl. Math. 88 (1998), 207–237, Corollaries 4.10–4.12, Theorems 4.14–4.19, Remark 4.18 and Table 1. <https://doi.org/10.1016/S0166-218X(98)00073-0>
