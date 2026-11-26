# Likelihood of the sample allele count by dynamic programming

With the notation of the [site allele frequency likelihood](site-allele-frequency-likelihood-and-em.md), let $G = (G_1, \dots, G_n)$ be the genotypes and $X = \sum_i G_i \in \{0, \dots, M\}$ the number of reference alleles in the sample. Under Hardy–Weinberg equilibrium the conditional law of $G$ given $X = k$ does not depend on $\psi$:

$$\Pr\{G = g \mid X = k\} = \frac{\prod_{i=1}^{n} \binom{m_i}{g_i}}{\binom{M}{k}} \quad \text{if } \textstyle\sum_i g_i = k,$$

and $0$ otherwise. Hence the likelihood of the allele count is

$$\mathcal{L}(k) = \Pr\{d \mid X = k\} = \binom{M}{k}^{-1} \sum_{g : \sum_i g_i = k} \prod_{i=1}^{n} \binom{m_i}{g_i} \mathcal{L}_i(g_i).$$

Define $z_{0,0} = 1$, $z_{0,l} = 0$ for $l \ne 0$, and for $1 \le j \le n$

$$z_{j,l} = \sum_{g=0}^{m_j} z_{j-1,\, l-g} \binom{m_j}{g} \mathcal{L}_j(g), \qquad 0 \le l \le \textstyle\sum_{i \le j} m_i,$$

with $z_{j-1, l'} = 0$ when $l'$ is out of range. Then $\mathcal{L}(k) = z_{n,k} / \binom{M}{k}$ for every $k$, computed in $O\bigl(M \max_i m_i \cdot n\bigr)$ operations.

## Depends on

- [Site allele frequency likelihood and its EM iteration](site-allele-frequency-likelihood-and-em.md)

## Expansion

Under Hardy–Weinberg equilibrium $\Pr\{G = g\} = \prod_i \binom{m_i}{g_i} \psi^{k} (1-\psi)^{M-k}$ and $\Pr\{X = k\} = \binom{M}{k} \psi^k (1-\psi)^{M-k}$ by Vandermonde's identity, so their ratio is free of $\psi$. By induction on $j$, $z_{j,l}$ is the sum over $(g_1, \dots, g_j)$ with $\sum g_i = l$ of $\prod_{i \le j} \binom{m_i}{g_i} \mathcal{L}_i(g_i)$. The paper notes that an earlier derivation omitted the factor $\binom{M}{k}^{-1}$, and gives rescaled versions of the recursion to avoid floating-point underflow.

## Sources

- H. Li, *A statistical framework for SNP calling, mutation discovery, association mapping and population genetical parameter estimation from sequencing data*, Bioinformatics 27 (2011), 2987–2993. <https://doi.org/10.1093/bioinformatics/btr509> (PMCID: PMC3198575) Sections 2.3.5–2.3.6, Equations (13)–(19).
