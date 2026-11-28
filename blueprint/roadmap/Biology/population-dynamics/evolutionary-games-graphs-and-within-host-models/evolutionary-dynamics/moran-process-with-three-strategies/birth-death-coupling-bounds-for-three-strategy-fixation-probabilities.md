# Birth–death coupling bounds for three-strategy fixation probabilities

**Model.** A population of fixed size $N$ contains $i$ individuals of type A, $j$ of type B and $N-i-j$ of type C, with state space $\Lambda_N=\{(i,j):i,j\ge0,\ i+j\le N\}$ and frequency-dependent fitnesses. In each Moran step one individual is chosen to reproduce with probability proportional to fitness and its offspring replaces a uniformly chosen individual. Let $p^{XY}_{ij}$ be the probability that an $X$ offspring replaces a $Y$ individual, and

$$Z^+_{ij}=p^{AB}_{ij}+p^{AC}_{ij},\qquad Z^-_{ij}=p^{BA}_{ij}+p^{CA}_{ij}$$

the probabilities that the number of A individuals goes up or down by one. Let $\alpha_{ij}$ be the probability that A eventually fixes, starting from $(i,j)$.

**Theorem (well-posedness).** The linear system for $\alpha$ (first-step equations on $\Lambda_N$ with boundary values $\alpha=1$ at all-A and $\alpha=0$ wherever $i=0$, the two-type edges $i+j=N$ and $j=0$ reducing to two-strategy Moran processes) has a unique solution; maxima and minima of $\alpha$ on any connected region are attained on its boundary. The same holds for the fixation probabilities $\beta,\gamma$ of B and C.

**Theorem (coupling bounds).** Let a birth–death chain on $\{0,\dots,N\}$ have birth and death probabilities $a_i,b_i$ and fixation probability $\pi_i$ at $N$.

- If $a_i\le Z^+_{ij}$, $b_i\ge Z^-_{ij}$ and $a_{i-1}\le1-Z^-_{ij}$ for all $(i,j)$, then $\alpha_{ij}\ge\pi_i$.
- If $a_i\ge Z^+_{ij}$, $b_i\le Z^-_{ij}$ and $b_{i+1}\le1-Z^+_{ij}$ for all $(i,j)$, then $\alpha_{ij}\le\pi_i$.

In particular, with $a_i^{\rm low}=\min_jZ^+_{ij}$, $b_i^{\rm low}=\max_jZ^-_{ij}$ (and $a_i^{\rm up}=\max_jZ^+_{ij}$, $b_i^{\rm up}=\min_jZ^-_{ij}$), one has $\pi_i^{\rm low}\le\alpha_{ij}\le\pi_i^{\rm up}$ for large enough $N$; the extremizing $j$ for $Z^+$ and $Z^-$ coincide.

**Theorem (constant fitnesses).** If the fitnesses are constants $f>g>h>0$ for A, B, C, then

$$\frac{1-(f/g)^{-i}}{1-(f/g)^{-N}}\le\alpha_{ij}\le\frac{1-(f/h)^{-i}}{1-(f/h)^{-N}},$$

with analogous bounds for $\beta_{ij}$ and $\gamma_{ij}$; hence, at fixed positive frequencies, the fittest type fixes with probability tending to $1$ as $N\to\infty$.

## Expansion

The comparison chain is built from the same uniform random variables as the Moran chain so that its A-count never exceeds (lower bound) or never falls below (upper bound) the Moran A-count; the extra conditions on $a_{i\mp1}$ prevent the two counts from crossing when they are adjacent. A birth–death chain with birth/death ratio $r_i=a_i/b_i$ has the explicit fixation probability $\pi_i=\big(1+\sum_{\ell=1}^{i-1}\prod_{k\le\ell}r_k^{-1}\big)/\big(1+\sum_{\ell=1}^{N-1}\prod_{k\le\ell}r_k^{-1}\big)$, increasing in every $r_k$. With constant fitnesses the ratio $Z^+_{ij}/Z^-_{ij}$ is a fitness-weighted average of $f/g$ and $f/h$, which yields the two-type Moran formulas as bounds.

## Depends on

- [Fixation probability of the Moran process](../../../../population-genetics/moran-model/eq-moran-fixation.md)

## Sources

- Eliza M. Ferreira, Armando G. M. Neves, "Fixation probabilities for the Moran process with three or more strategies: general and coupling results", arXiv:1811.09552: Proposition 1 and Theorem 1 (maximum principle, uniqueness), Theorems 2–3 (coupling bounds), Theorem 4 and Corollary 1 (constant fitnesses), Proposition 2 and Theorem 5 (general comparison chains), Propositions 3–4 (birth–death fixation). <https://doi.org/10.48550/arXiv.1811.09552> Published version: Journal of Mathematical Biology 81 (2020) 277–314, <https://doi.org/10.1007/s00285-020-01510-0>.
