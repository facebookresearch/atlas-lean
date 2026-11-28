# Finite-horizon moment recursions for reproductive output

**Setting.** A life cycle has $s$ transient stages and one absorbing state (death). Its column-stochastic transition matrix is

$$P = \begin{pmatrix} U & 0 \\ \mathbf m^{\mathsf T} & 1 \end{pmatrix},$$

with $U$ the $s \times s$ transient matrix ($U_{ij}$ is the probability of moving from stage $j$ to stage $i$), $\mathbf m$ the vector of mortality probabilities, and spectral radius of $U$ less than $1$, so every individual eventually dies. A transition $j \to i$ pays a random reward $r_{ij}$ (offspring produced), drawn independently of the rest of the path, with $r_{ij} = 0$ for transitions out of the dead state. Let $R_k$ be the $(s+1) \times (s+1)$ matrix of $k$-th moments, $(R_k)_{ij} = \mathbb{E}[r_{ij}^k]$, with $R_0$ the all-ones matrix. For $t$ steps remaining before a terminal time, let $\rho_k(t)$ be the vector whose $j$-th entry is the $k$-th moment of the reward still to be collected by an individual now in state $j$; $\rho_0 = \mathbf 1$ and $\rho_k(0) = 0$ for $k \ge 1$.

**Proposition 1 (moment recursions).** With $\circ$ the entrywise product,

$$\rho_k(t+1) = \sum_{j=0}^{k} \binom{k}{j}\,(P \circ R_{k-j})^{\mathsf T}\rho_j(t), \qquad k \ge 1;$$

in particular

$$\rho_1(t+1) = (P\circ R_1)^{\mathsf T}\mathbf 1 + P^{\mathsf T}\rho_1(t),$$

$$\rho_2(t+1) = (P\circ R_2)^{\mathsf T}\mathbf 1 + 2(P\circ R_1)^{\mathsf T}\rho_1(t) + P^{\mathsf T}\rho_2(t),$$

$$\rho_3(t+1) = (P\circ R_3)^{\mathsf T}\mathbf 1 + 3(P\circ R_2)^{\mathsf T}\rho_1(t) + 3(P\circ R_1)^{\mathsf T}\rho_2(t) + P^{\mathsf T}\rho_3(t).$$

**Lifetime limit.** Because death is certain and pays nothing afterwards, $\rho_k(t)$ converges as $t \to \infty$ to the vector $\rho_k$ of $k$-th moments of lifetime reward. On the transient stages this limit is the closed form of [moments of lifetime reproductive output](moments-of-lifetime-reproductive-output.md) with one absorbing state, from which the variance, coefficient of variation and skewness of lifetime reproduction by initial stage follow.

**Variable environments.** If the environment moves among finitely many states by a column-stochastic matrix (stochastic, periodic or a fixed sequence) and each state has its own transition and reward-moment matrices, the pairs (stage, environment) form one Markov chain, built with the vec-permutation matrix, to which Proposition 1 applies directly. Averaging the moment vectors over the stationary environment distribution gives moments by initial stage alone.

## Expansion

Condition on the first transition. An individual in state $j$ moving to $i$ collects $r_{ij}$ now and $\rho(t)$-distributed reward from $i$ afterwards, independently, so $\mathbb{E}[(r_{ij} + \text{future})^k] = \sum_{m}\binom{k}{m}\mathbb{E}[r_{ij}^{k-m}]\,\rho_m(t)_i$; averaging over $i$ with weights $P_{ij}$ gives the matrix recursion. In the lifetime limit the term $j = k$ contributes only through transient stages (the dead state has $\rho_k = 0$ for $k \ge 1$), so passing to the limit in the recursion gives the fixed-point equation that the closed form solves. Applied to laboratory cohorts of genetically identical nematodes, the computed variance of lifetime egg production matched the observed variance when the empirical moments of daily reproduction were used, while Poisson or fixed rewards seriously underestimated it: variability in lifetime reproduction is expected from individual stochasticity alone and is evidence of heterogeneity only beyond this baseline.

## Depends on

- [Moments of lifetime reproductive output in a Markov chain with rewards](moments-of-lifetime-reproductive-output.md)

## Sources

- H. Caswell, "Beyond R0: demographic models for variability of lifetime reproductive output", PLoS ONE 6(6) (2011) e20809, sections "Analysis" and "Lifetime reproduction in variable environments", Proposition 1 and Eqs. (3), (10)–(13), (24)–(27), (37)–(53), <https://doi.org/10.1371/journal.pone.0020809>, PMCID PMC3126812.
