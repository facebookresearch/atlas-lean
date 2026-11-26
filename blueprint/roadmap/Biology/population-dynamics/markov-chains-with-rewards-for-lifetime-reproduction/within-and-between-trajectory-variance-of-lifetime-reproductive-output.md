# Within- and between-trajectory variance of lifetime reproductive output

**Setting.** Work in the Markov chain with rewards of [moments of lifetime reproductive output](moments-of-lifetime-reproductive-output.md): a life cycle with transient block $U$, column-stochastic transition matrix $P$, and reward-moment matrices $R_k$ with $(R_k)_{ij} = \mathbb E[r_{ij}^k]$ for the offspring produced on the transition $j \to i$. All individuals share the same rates, so all variance in lifetime reproductive output (LRO) is *individual stochasticity*. Three standard reward models, each determined by the mean matrix $R_1$, are:

- **Bernoulli** (at most one offspring per step): $R_3 = R_2 = R_1$;
- **Poisson**: $R_2 = R_1 + R_1 \circ R_1$ and $R_3 = R_1 + 3\,R_1 \circ R_1 + R_1 \circ R_1 \circ R_1$;
- **Fixed** (every individual in a transition produces exactly the mean): $R_2 = R_1 \circ R_1$ and $R_3 = R_1 \circ R_1 \circ R_1$.

**Proposition (variance partition).** Let $V(\tilde\rho)$ be the vector of variances of LRO by starting state under a given reward model with mean matrix $R_1$, computed from the moment formula with that model's $R_2$. Then

$$V(\tilde\rho) = V_{\text{within}} + V_{\text{between}},$$

where $V_{\text{between}}$, the variance among life trajectories (sequences of stages visited), equals $V(\tilde\rho)$ computed under the fixed reward model with the same $R_1$, and $V_{\text{within}} = V(\tilde\rho) - V_{\text{between}}$ is the variance due to random reproduction along a given trajectory. Under the Bernoulli or Poisson model, $V_{\text{within}} \ge 0$ entrywise.

## Depends on

- [Moments of lifetime reproductive output in a Markov chain with rewards](moments-of-lifetime-reproductive-output.md)

## Expansion

Condition on the trajectory $X$ of stages. Given $X$, LRO is a sum of independent rewards, one per transition taken, so the law of total variance gives $V(\rho) = \mathbb E[V(\rho \mid X)] + V(\mathbb E[\rho \mid X])$. The fixed reward model sets each reward equal to its conditional mean, which kills the first term and leaves $\mathbb E[\rho \mid X]$ unchanged; hence the fixed-reward variance is the between-trajectory term, and subtraction gives the within-trajectory term. Under the Poisson model the per-transition reward variance is $R_1$ (entrywise), so the within-trajectory part is an expected sum of nonnegative terms; under the Bernoulli model it is $R_1 - R_1 \circ R_1 \ge 0$ since $R_1$ entries are probabilities. The source notes that published studies agree that individual stochasticity can account for a high proportion of observed variance in LRO, so high empirical variance does not by itself indicate heterogeneity.

## Sources

- S. F. van Daalen and H. Caswell, "Lifetime reproductive output: individual stochasticity, variance, and sensitivity analysis", *Theoretical Ecology* 10 (2017) 355–374, Eqs. (5)–(9) (reward models) and Eq. (25) with the subsection "Partitioning variance: within and between pathways". <https://doi.org/10.1007/s12080-017-0335-2> (PMC6979506)
