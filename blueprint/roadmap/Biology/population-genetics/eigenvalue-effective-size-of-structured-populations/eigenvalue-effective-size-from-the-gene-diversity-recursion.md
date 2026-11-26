# Eigenvalue effective size from the gene diversity recursion

**Setting.** A population is divided into $s$ subpopulations with sizes $2Nu_i$ genes, $\sum_i u_i = 1$, and a biallelic gene evolves in discrete generations; $X_t = (X_t^1, \dots, X_t^s)$ are the subpopulation allele frequencies, a finite Markov chain with transition matrix $P$. Assume that no subpopulation is isolated, so that the only absorbing classes are fixation of either allele in all subpopulations. Let $\lambda = \lambda_3(P)$ be the largest non-unit eigenvalue of $P$. Since the Wright–Fisher model with $N$ diploids has $\lambda_3 = 1 - 1/(2N)$, the **eigenvalue effective size** is defined by

$$N_{eE} = \frac{1}{2(1 - \lambda)}.$$

Under these conditions $\lambda$ is real and positive and governs the asymptotic rate at which the probability of non-fixation, and any nonnegative function vanishing at fixation, decays: $\mathbb{E}_\pi \phi(X_t) \asymp \lambda^t$.

**Gene diversity.** Let $H_t^{ij} = X_t^i(1 - X_t^j) + X_t^j(1 - X_t^i)$ be the probability that genes drawn from subpopulations $i$ and $j$ differ, and $\mathbf{H}_t = (\mathbb{E}_\pi H_t^{ij})_{i,j}$ the vector of predicted gene diversities.

**Theorem.**
1. If $\mathbf{H}_t = A\,\mathbf{H}_{t-1}$ for a nonnegative $s^2 \times s^2$ matrix $A$, then $\lambda_3(P) = \lambda_{\max}(A) = \max_a \lambda_{\max}(A_{aa})$ over the irreducible diagonal blocks of $A$, and hence

$$N_{eE} = \frac{1}{2\,(1 - \lambda_{\max}(A))}.$$

2. Such a recursion holds whenever the backward subpopulation ancestry of two distinct genes is a Markov chain with transition matrix $Q = (Q_{ij,kl})$ on pairs of subpopulations: $A_{ij,kl}$ is $Q_{ij,kl}$ multiplied by the probability that two lineages with parents in a common subpopulation $k$ do not coalesce, with corrections for sampling with replacement within a subpopulation.
3. (Large populations.) If the subpopulation sizes grow with $N$ so that coalescence probabilities are of order $N^{-\beta}$, $0 < \beta \le 1$, and the migration matrix converges to $Q(0)$ with equilibrium distribution $\rho(0)$ on pairs, then

$$N_{eE} = \frac{N^\beta}{C} + o(N^\beta), \qquad C = \sum_{i,j,k} \rho_{ij}(0)\,\sigma_{ijk}\,\frac{Q_{ij,kk}(0)}{u_k^\beta},$$

where $\sigma_{ijk}$ are limiting standardized offspring-number covariances. $C$ is the equilibrium coalescence rate on time scale $2N^\beta$, so $N_{eE}$ agrees asymptotically with the coalescence effective size when the latter exists.

## Expansion

Predicted gene diversities are expectations of quadratic functions of $X_t$ that vanish exactly at fixation, so by the Perron–Frobenius decomposition of $P$ they decay at rate $\lambda_3(P)$; matching this with the decay $A^t \approx \lambda_{\max}(A)^t r\rho$ of the linear recursion identifies the two eigenvalues. Tracing two lineages back one generation, they either coalesce (contributing zero diversity) or move to a pair of parental subpopulations $(k,l)$ with probability $Q_{ij,kl}$, which yields the recursion. In the large-population limit $A(\epsilon) = A(0) + \epsilon \dot A + o(\epsilon)$ with $A(0)$ stochastic, and first-order eigenvalue perturbation gives $1 - \lambda_{\max}(A) \approx \epsilon\,\rho(0)\dot A\,\mathbf{1}$, the averaged coalescence rate. Island models, strong and weak migration limits, and Ewens' 1982 results appear as special cases.

## Depends on

- [Effective population size](../effective-population-size/README.md)
- [Wright's island model](../wright-s-island-model/README.md)

## Sources

- O. Hössjer, "On the eigenvalue effective size of structured populations", Journal of Mathematical Biology (2015), Eqs (19)–(25), Theorem 1 and Corollary 1, Theorem 2 and Corollary 2 (Eq 32), Theorem 3 (Eqs 39–41), Theorems 4–5 (Eqs 80–83), <https://doi.org/10.1007/s00285-014-0832-5>, PMCID PMC4532751.
