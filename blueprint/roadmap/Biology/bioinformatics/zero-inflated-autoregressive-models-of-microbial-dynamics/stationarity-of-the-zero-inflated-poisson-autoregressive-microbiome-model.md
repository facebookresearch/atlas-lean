# Stationarity of the zero-inflated Poisson autoregressive microbiome model

Let $Y_{imt}$ be the absolute abundance of taxon $m = 1, \dots, M$ in subject $i$ at time $t$. The autoregressive zero-inflated mixed-effects model (ARZIMM) posits, conditionally on the information $\nu_{i(t-1)}$ available at time $t-1$,

$$Y_{imt} \mid \nu_{i(t-1)} \sim \begin{cases} 0 & \text{with probability } p_{im},\\ \text{Poisson}(e^{\theta_{imt}}) & \text{with probability } 1 - p_{im},\end{cases}$$

with time-independent structural-zero probabilities modelled by $\operatorname{logit}(p_i) = AW_i + a_i$, $a_i \sim N(0, \Sigma_a)$, and log-means

$$\theta_{it} = B\,\tilde Y_{i(t-1)} + C Z_i + \eta_i,\qquad \tilde Y_{i(t-1)} = \left(\log(Y_{i1(t-1)} + 1), \dots, \log(Y_{iM(t-1)} + 1)\right)',$$

where $W_i, Z_i$ are covariates, $\eta_i$ are subject-level random intercepts (projected on the initial abundances as $\eta_i = \Pi\tilde Y_{i0} + b_i$ with $\Pi$ diagonal and $b_i \sim N(0, \Sigma_b)$), and the $M \times M$ matrix $B$ encodes microbial interactions: $B_{mj}$ is the effect of taxon $j$'s abundance on taxon $m$'s growth.

**Theorem.** If $\eta_i$ and $p_i$ are known and all eigenvalues of $B$ lie inside the unit circle, then there exists a strict-sense stationary ergodic process $\{Y_{it}\}_{t \in \mathbb{N}}$ following the model.

Given stationarity, community stability is summarized by the largest eigenvalue modulus $\max|\lambda_B|$: it bounds both the return rate towards the stationary distribution after a perturbation and the reactivity, so smaller values indicate a more stable community. In practice $B$ is estimated by penalized (lasso-type) maximum likelihood with an EM treatment of the zero labels.

## Expansion

The process is a Markov chain on count vectors whose log-mean responds linearly to $\log(Y + 1)$. A spectral radius below $1$ makes this linear feedback a contraction, which yields a drift condition and, by Markov-chain theory for observation-driven count time series, a unique invariant law and ergodicity; zero inflation with fixed probabilities only mixes in a point mass and does not affect the contraction. The stability measures are those of multivariate first-order autoregressive community models, where the variance and the approach rate of the stationary distribution are governed by the eigenvalues of the interaction matrix.

## Sources

- L. He, C. Wang, J. Hu, Z. Gao, E. Falcone, S. M. Holland, M. J. Blaser and H. Li, "ARZIMM: a novel analytic platform for the inference of microbial interactions and community stability from longitudinal microbiome study", *Frontiers in Genetics* 13 (2022), 777877, Materials and Methods, Eqs. (1)–(4), and "Stability Properties", Theorem 1. <https://doi.org/10.3389/fgene.2022.777877> (PMC8914110)
