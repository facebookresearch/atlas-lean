# Entropy of posterior ancestries

For a case in a reconstructed outbreak, let $K$ be the number of distinct infectors that appear in a posterior sample of transmission trees, and $f_1, \dots, f_K > 0$ their posterior frequencies ($\sum_k f_k = 1$). The entropy of the posterior ancestry is

$$H = -\sum_{k=1}^{K} f_k \log f_k .$$

It satisfies $0 \le H \le \log K$, with $H = 0$ exactly when a single infector is supported by every posterior sample and $H = \log K$ exactly when the $K$ candidate infectors are equally supported.

## Depends on

- [Epidemiological pseudo-likelihood with unobserved intermediate cases](epidemiological-pseudo-likelihood-with-unobserved-intermediate-cases.md)

## Expansion

Each term $-f_k \log f_k$ is nonnegative on $(0,1]$ and vanishes only at $f_k = 1$, which gives the lower bound and its equality case; the upper bound is Jensen's inequality for the concave logarithm, $\sum_k f_k \log(1/f_k) \le \log \sum_k f_k (1/f_k) = \log K$, with equality iff all $f_k$ are equal. Unlike the posterior support of the single most frequent infector, the entropy also distinguishes a choice between two candidates from a diffuse spread over many, so it measures how informative the combined genomic and epidemiological data are about who infected a given case.

## Sources

- Campbell F, Strang C, Ferguson N, Cori A, Jombart T. When are pathogen genome sequences informative of transmission events? *PLoS Pathogens* (2018), Results, "Transmission divergence", and Materials and methods, "Estimating transmission divergence from simulated outbreaks" and "Outbreak reconstruction", equation (1). DOI <https://doi.org/10.1371/journal.ppat.1006885>. PMCID PMC5821398.
