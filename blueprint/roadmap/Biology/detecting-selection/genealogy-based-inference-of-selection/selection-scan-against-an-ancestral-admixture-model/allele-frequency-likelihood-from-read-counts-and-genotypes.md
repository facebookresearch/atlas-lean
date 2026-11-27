# Allele-frequency likelihood from read counts and hard genotype calls

At one biallelic SNP, consider a population with reference-allele frequency $p \in [0,1]$ under Hardy–Weinberg proportions. Suppose $N$ individuals have hard diploid genotype calls carrying $X$ reference alleles among $2N$ chromosomes, and $M$ further individuals have only sequence reads, individual $i$ showing $R_i$ reference reads out of $T_i$ reads. Let $\varepsilon \in (0, 1/2)$ be a per-read error probability and $B(k, n, q) = \binom{n}{k} q^k (1-q)^{n-k}$. Treating individuals and reads as independent given genotypes, the likelihood of $p$ is

$$L(p; D) = B(X, 2N, p)\prod_{i=N+1}^{N+M}\Big\{p^2 B(R_i, T_i, 1-\varepsilon) + 2p(1-p) B(R_i, T_i, \tfrac12) + (1-p)^2 B(R_i, T_i, \varepsilon)\Big\}.$$

The maximum-likelihood frequency $\hat p = \arg\max_p L(p; D)$ is used as the population frequency estimate, and the log-likelihood $\ell(p; D) = \log L(p; D)$ is the building block of frequency-based tests.

## Depends on

- [Hardy–Weinberg proportions](../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Expansion

Each read-only individual contributes a mixture over its three possible genotypes, with Hardy–Weinberg weights $p^2, 2p(1-p), (1-p)^2$ and read-count likelihoods that are binomial with success probability $1-\varepsilon$ for a reference homozygote, $1/2$ for a heterozygote and $\varepsilon$ for an alternative homozygote. Genotyped individuals contribute the binomial likelihood of their allele count. The approach avoids calling diploid genotypes from one or two reads, which would bias frequencies, and lets individuals with very different coverage share one model. Mathieson et al. set $\varepsilon = 0.001$ and maximize the likelihood numerically per population and SNP.

## Sources

- I. Mathieson, I. Lazaridis, N. Rohland, et al., "Genome-wide patterns of selection in 230 ancient Eurasians", Nature 528 (2015), 499–503, <https://doi.org/10.1038/nature16152> (PMC4918750), Methods "Genome-wide scan for selection".
