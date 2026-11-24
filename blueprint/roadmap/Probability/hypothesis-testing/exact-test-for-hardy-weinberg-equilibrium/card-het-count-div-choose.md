# Levene's formula is the conditional law under random union of gametes

Let $N, n_A, h \in \mathbb{N}$. Among the $\binom{2N}{n_A}$ placements of the $n_A$ copies of $A$ in the $2N$ gamete slots, the proportion with exactly $h$ [heterozygous individuals](het-count.md) is [Levene's probability](levene-prob.md) $L(N, n_A, h)$:

$$\frac{\#\{s : |s| = n_A,\ s \text{ has } h \text{ heterozygous individuals}\}}{\binom{2N}{n_A}} = L(N, n_A, h).$$

No hypothesis $n_A \le 2N$ is needed: for $n_A > 2N$ there is no placement, $\binom{2N}{n_A} = 0$ and the left side is $0/0$, read as $0$, matching $L(N, n_A, h) = 0$; the statement is meaningful for $n_A \le 2N$. The model is the uniform law on placements, which is the law of independent gametes conditioned on the allele count $n_A$.

## Sources

- H. Levene, *On a matching problem arising in genetics*, Ann. Math. Statist. 20 (1949), 91–94.
- J. E. Wigginton, D. J. Cutler and G. R. Abecasis, *A note on exact tests of Hardy–Weinberg equilibrium*, Amer. J. Hum. Genet. 76 (2005), 887–893.
