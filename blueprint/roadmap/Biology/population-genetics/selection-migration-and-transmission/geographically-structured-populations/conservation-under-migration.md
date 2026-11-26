# Which weighted frequency migration conserves

Let $P = (p_{ij})$ be a backward migration matrix on finitely many demes: $p_{ij} \ge 0$ is the fraction of the genes of deme $i$ after migration that came from deme $j$, and $\sum_jp_{ij} = 1$. Migration maps the vector of allele frequencies $x$ to $Px$. For weights $w$, the weighted frequency $\bar x = \sum_iw_ix_i$ is unchanged by migration for every $x$ if and only if $w^TP = w^T$: indeed $w^TPx = w^Tx$ for all $x$ exactly when $w^TP - w^T = 0$. If $P$ is irreducible, the Perron–Frobenius theorem gives a unique positive left eigenvector of $P$ for the eigenvalue $1$ with $\sum_iw_i = 1$, so there is exactly one conserved weighted frequency, the one weighted by the stationary law of the backward lineage-migration chain; this average is the frequency that governs the strong-migration limit (Nagylaki 1980).

Census weights are conserved exactly under conservative migration. Suppose deme $i$ has $N_i$ genes and a proportion $m_{ij}$ of them migrates to deme $j$, with the balance $N_i\sum_{j \ne i}m_{ij} = \sum_{j \ne i}N_jm_{ji}$, the condition that migration does not alter the deme sizes (conservative migration, Nagylaki 1980). Then $p_{ij} = N_jm_{ji}/N_i$ for $j \ne i$, and with $w_i = N_i/\sum_kN_k$,

$$(w^TP)_j = \frac{1}{\sum_kN_k}\Bigl(\sum_{i \ne j}N_jm_{ji} + N_j - \sum_{i \ne j}N_im_{ij}\Bigr) = w_j,$$

where the last step is the balance condition at deme $j$; conversely $w^TP = w^T$ with census weights is the balance condition. In a source–sink pair with one-way migration from deme $1$ to deme $2$, $p_{21} > 0 = p_{12}$, so $w = (1, 0)$: only the source frequency is conserved, and the census average is not.

## Depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Expansion

1. The migration step $x \mapsto Px$ and the equivalence of conservation with $w^TP = w^T$.
2. Existence and uniqueness of positive normalized left eigenvectors for irreducible $P$.
3. Census weights under the balance condition, and the source–sink example.
4. The continuous-time version: with backward migration rates $q_{ij}$, $\sum_iw_ix_i$ has zero migration drift exactly when $w^TQ = 0$ for the rate matrix $Q$.

## Sources

- T. Nagylaki, The strong-migration limit in geographically structured populations, J. Math. Biol. 9 (1980), 101–114. <https://doi.org/10.1007/BF00275916>
- E. Seneta, *Non-negative Matrices and Markov Chains*, 2nd ed., Springer (1981), Chapter 1.
