# Sampling variance of single-SNP genetic relationships

Let $x \in \{0, 1, 2\}$ and $x'$ be the allele counts of two individuals at a biallelic SNP with allele frequency $p \in (0, 1)$, independent and each $\mathrm{Binomial}(2, p)$ (Hardy–Weinberg, unrelated, non-inbred). Write $q = 1 - p$ and $w = (x - 2p)/\sqrt{2pq}$, $w' = (x' - 2p)/\sqrt{2pq}$. Then

1. the off-diagonal single-SNP relationship $A_{jk} = w w'$ has mean $0$ and variance exactly $1$, for every $p$;
2. the naive diagonal $w^2$ has mean $1$ and variance $\dfrac{1 - 2pq}{2pq}$, which grows without bound as $p \to 0$ or $p \to 1$;
3. the GCTA diagonal estimator

$$\tilde A_{jj} = 1 + \frac{x^2 - (1 + 2p)x + 2p^2}{2pq}$$

has mean $1$ and variance exactly $1$, for every $p$.

Averaging over $N$ independent SNPs therefore gives relationship estimates whose sampling variance is $1/N$ both off and on the diagonal.

## Expansion

(1) $E[w^2] = 1$ and independence give $\mathrm{Var}(w w') = E[w^2]E[w'^2] = 1$. (2) The fourth central moment of $\mathrm{Binomial}(2, p)$ is $2pq$, so $E[w^4] = 2pq/(2pq)^2 = 1/(2pq)$ and $\mathrm{Var}(w^2) = 1/(2pq) - 1$. (3) The numerator $x^2 - (1 + 2p)x + 2p^2$ takes the values $2p^2$, $-2pq$, $2q^2$ at $x = 0, 1, 2$, so $\tilde A_{jj} - 1$ takes the values $p/q$, $-1$, $q/p$ with probabilities $q^2$, $2pq$, $p^2$. Its mean is $pq - 2pq + pq = 0$ and its second moment is $p^2 + 2pq + q^2 = 1$.

## Depends on

- [GCTA diagonal relationship estimator](../../quantitative-genetics/genomic-relationship-matrices/grm-diag.md)
- [Genetic relationship matrix](grm.md)

## Sources

- J. Yang, B. Benyamin, B. P. McEvoy et al., "Common SNPs explain a large proportion of the heritability for human height", *Nature Genetics* 42 (2010), 565–569, <https://doi.org/10.1038/ng.608> (PMC3232052). Online Methods, the variances stated before equation [5], equation [5] and equation [6].
