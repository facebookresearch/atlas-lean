# Site allele frequency likelihood and its EM iteration

Let $n$ samples have ploidies $m_1, \dots, m_n$, total $M = \sum_i m_i$, and [genotype likelihoods](genotype-likelihood-of-biallelic-reads.md) $\mathcal{L}_i(g)$, $0 \le g \le m_i$. Assume Hardy–Weinberg equilibrium with reference allele frequency $\psi \in [0, 1]$, so that $g_i \sim \mathrm{Binom}(m_i, \psi)$ with mass function $f_{m}(g; \psi) = \binom{m}{g} \psi^g (1 - \psi)^{m-g}$, independently across samples. The likelihood of $\psi$ is

$$\mathcal{L}(\psi) = \prod_{i=1}^{n} \sum_{g=0}^{m_i} \mathcal{L}_i(g)\, f_{m_i}(g; \psi).$$

Treating the genotypes as missing data, the expectation–maximization update is

$$\psi^{(t+1)} = \frac{1}{M} \sum_{i=1}^{n} \frac{\sum_{g=0}^{m_i} g\, \mathcal{L}_i(g)\, f_{m_i}(g; \psi^{(t)})}{\sum_{g=0}^{m_i} \mathcal{L}_i(g)\, f_{m_i}(g; \psi^{(t)})}.$$

## Depends on

- [Genotype likelihood of biallelic sequencing reads](genotype-likelihood-of-biallelic-reads.md)

## Expansion

The E-step computes the posterior mean of $g_i$ under the current $\psi^{(t)}$; the M-step maximizes the expected complete-data binomial log-likelihood $\sum_i \mathbb{E}[g_i] \log \psi + (m_i - \mathbb{E}[g_i]) \log(1 - \psi)$, whose maximizer is the expected reference count divided by $M$. As for any EM iteration, $\mathcal{L}(\psi^{(t)})$ is non-decreasing in $t$. The paper switches to a direct numerical maximizer (Brent's method) when EM converges slowly.

## Sources

- H. Li, *A statistical framework for SNP calling, mutation discovery, association mapping and population genetical parameter estimation from sequencing data*, Bioinformatics 27 (2011), 2987–2993. <https://doi.org/10.1093/bioinformatics/btr509> (PMCID: PMC3198575) Section 2.3.1, Equations (3)–(5).
