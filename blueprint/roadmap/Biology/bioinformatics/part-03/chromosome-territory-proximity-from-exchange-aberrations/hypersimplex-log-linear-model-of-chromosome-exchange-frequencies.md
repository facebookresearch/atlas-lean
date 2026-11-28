# Hypersimplex log-linear model of chromosome exchange frequencies

**Data.** For $m$ non-homologous chromosomes, let $f(j,k)$, $1\le j<k\le m$, be the number of cells in which at least one exchange-type chromosome aberration between chromosomes $j$ and $k$ was observed (an upper-triangular table with $\binom m2$ cells; $m=22$ autosomes in human data).

**No-proximity model.** The exchange partner pair is a random variable on $\{(j,k):j<k\}$ with

$$
p_{jk}=\theta_j\theta_k,\qquad \theta_1,\dots,\theta_m>0,
$$

that is, $\log p_{jk}=\beta_j+\beta_k$. This is the log-linear model with $m\times\binom m2$ design matrix $A(m)$ whose columns $e_j+e_k$ are the vertices of the second hypersimplex in $\mathbb R^m$. Its minimal sufficient statistic is the vector of marginal totals

$$
u_k=\sum_{j\ne k} f(j,k),\qquad k=1,\dots,m,
$$

which measures the propensity of each chromosome to take part in exchanges.

**Single-pair proximity model.** For a fixed pair $\{r,s\}$, $p_{rs}=\theta_r\theta_s\mu_{rs}$ and $p_{jk}=\theta_j\theta_k$ otherwise; $\mu_{rs}>1$ means excess exchanges, interpreted as spatial proximity of the two chromosome territories. Its design matrix adds one indicator row for cell $(r,s)$, so the model is nested one dimension above the no-proximity model.

**Inference.**

1. *MLE.* For both models the maximum likelihood table $\hat f$ is the unique table with the same sufficient statistics as $f$ whose normalization lies on the model (Birch's theorem); it is computed by iterative proportional scaling.
2. *Exact goodness of fit.* The conditional (fiber) distribution given $u$ is sampled by a Metropolis–Hastings walk on the fiber $\mathcal F(u)$ (lattice points of a polytope) using a Markov basis of the hypersimplex: for $i<j<k<\ell$, the moves $m[i,j;k,\ell]=+e_{ij}+e_{k\ell}-e_{ik}-e_{j\ell}$ and $m[i,\ell;j,k]=+e_{i\ell}+e_{jk}-e_{ik}-e_{j\ell}$ and their negatives, $4\binom m4$ moves in all (a Gröbner basis of the toric ideal of $A(m)$). The $p$-value of Pearson's statistic $\chi^2=\sum_{j<k}(F_{jk}-\hat f_{jk})^2/\hat f_{jk}$ is the fraction of sampled tables with $\chi^2(F)\ge\chi^2(f)$.
3. *Proximity test.* The likelihood ratio statistic $G^2=2\sum_{j<k}\hat f^1_{jk}\log(\hat f^1_{jk}/\hat f^0_{jk})$ between the single-pair and no-proximity MLEs is asymptotically $\chi^2_1$ under the no-proximity null.

## Expansion

Exchanges require two broken chromosomes to be close in the nucleus, so a chromosome pair exchanging more often than its marginal propensities predict indicates adjacent territories. Because the table is sparse (it even has a zero cell), asymptotic $\chi^2$ calibration of the overall fit is unreliable, which is why the fiber is explored with the algebraic Markov basis: moving along a basis element changes four cells by $\pm1$ while preserving every row-plus-column marginal $u_k$, and the basis connects every fiber. On 3,585 irradiated human lymphocytes the no-proximity model fits overall, with the pairs $\{1,22\}$ and $\{13,14\}$ showing significant excess exchanges.

## Depends on

- [Markov basis](../../../../RingTheory/ideals-and-constructions/toric-ideals-and-markov-bases/is-markov-basis.md)

## Proof depends on

- [Birch's theorem, uniqueness](../../../systems-biology/complex-balancing-and-the-deficiency-zero-theore/eq-of-sub-mem-log-orthogonal.md)

## Sources

- Javier Arsuaga, Ido Heskia, Serkan Hosten, Tatsiana Maskalevich, "Uncovering Proximity of Chromosome Territories using Classical Algebraic Statistics", arXiv:1406.0148 (2014), Section 2 (log-linear models, MLE, Markov basis MCMC, log-ratio test) and Section 3, <https://doi.org/10.48550/arXiv.1406.0148>.
- B. Sturmfels, *Gröbner Bases and Convex Polytopes*, AMS (1996), Theorem 9.1 (Gröbner basis of the second hypersimplex).
