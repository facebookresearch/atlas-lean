# Log least-squares estimation of branch $F_{ST}$ and the population tree

**Setting.** $K$ sampled populations (or diploid individuals, each treated as a population of two gametes) sit at the tips of a binary population tree under the branch model of [shared and non-shared $F_{ST}$](shared-and-non-shared-fst-on-a-population-tree.md), with $2(K-1)$ branch parameters $\theta_q$. At each SNV let $\hat p_k$ be the sample allele frequency from $n_k$ gametes, and set $N_k = \hat p_k(1-\hat p_k)$ and $D_{kk'} = \hat p_k(1-\hat p_{k'}) + \hat p_{k'}(1-\hat p_k)$. With sums over SNVs, define for $k\ne k'$

$$S_{kk'} = \frac{2n_k}{n_k-1}\,\frac{\sum N_k}{\sum D_{kk'}}.$$

SNVs monomorphic in $k$ and $k'$ jointly contribute to neither sum. $S_{kk'} \ne S_{k'k}$ in general.

**Proposition.** For $k\ne k'$,

$$\mathbb{E}[S_{kk'}] \approx 1 - \operatorname{Cor}[x_k, y_k \mid p_{M(kk')}] = \prod_{q\in R(kk')}(1-\theta_q),$$

where $R(kk')$ is the set of branches ancestral to $k$ but not to $k'$.

**Estimator.** Write $\beta_q = \log(1-\theta_q)$ and solve the constrained least-squares problem

$$\hat\beta = \arg\min_{\beta \le 0}\ \xi(\beta),\qquad \xi(\beta) = \sum_{k\ne k'}\Big(\log S_{kk'} - \sum_{q\in R(kk')}\beta_q\Big)^2,$$

then set $\hat\theta_q = 1-\exp(\hat\beta_q)$ and plug these into the closed forms for $F_{ST}^{W}$ and $F_{ST}^{H}$. There are $K(K-1)$ statistics $S_{kk'}$ for $2(K-1)$ unknowns, so both coefficients are identifiable from pairwise moments, unlike an unstructured-covariance model.

**Tree search.** All binary trees with $K$ tips have the same number of parameters, so they can be compared by the minimized $\xi$. Start from the star tree; $K-2$ times, insert an intermediate ancestor above the pair of children of the root that most reduces $\xi$; then, for each tip in random order, try regrafting its parent onto each of the $2(K-1)$ branches and keep the tree minimizing $\xi$.

## Depends on

- [Shared and non-shared $F_{ST}$ on a population tree](shared-and-non-shared-fst-on-a-population-tree.md)

## Expansion

For $k\ne k'$, $\hat p_k(1-\hat p_{k'})$ is unbiased for $p_k(1-p_{k'})$ and $\tfrac{n_k}{n_k-1}N_k$ is unbiased for $p_k(1-p_k)$, so the ratio of sums estimates the ratio of within-population to between-population mismatch, which is $\prod_{R(kk')}(1-\theta_q)$; the approximation is the usual ratio-of-expectations step, accurate when the denominator has a small coefficient of variation over many SNVs. Taking logarithms makes the model linear in $\beta$. The classical pairwise Hudson estimator $\hat F_{ST}^{H}(kk') = \sum N_{kk'}/\sum D_{kk'}$ with $N_{kk'} = (\hat p_k-\hat p_{k'})^2 - \frac{\hat p_k(1-\hat p_k)}{n_k-1} - \frac{\hat p_{k'}(1-\hat p_{k'})}{n_{k'}-1}$ uses only two populations; the joint fit borrows information about ancestral frequencies across all of them and was more efficient in simulations when the structure is close to tree-like.

## Sources

- Mary-Huard T, Balding D. Fast and accurate joint inference of coancestry parameters for populations and/or individuals. *PLoS Genetics* 19(1):e1010054 (2023), Proposition 1 (Eq. 10), Eqs. 5-7, 9 and 11. <https://doi.org/10.1371/journal.pgen.1010054>. PMCID: PMC9888729.
