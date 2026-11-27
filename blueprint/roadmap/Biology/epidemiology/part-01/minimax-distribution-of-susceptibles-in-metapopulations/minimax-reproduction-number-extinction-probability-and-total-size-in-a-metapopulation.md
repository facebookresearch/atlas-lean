# Minimax reproduction number, extinction probability and total size in a metapopulation

**Setting.** In the multitype branching-process approximation of an early metapopulation epidemic, susceptibles have stationary distribution $\pi$ over $m$ groups, infectives migrate with an irreducible rate matrix $Q$, and infection and recovery rates in group $i$ are $\beta_i\pi_i$ and $\gamma_i$. The expected time an individual first infected in group $i$ spends in group $j$ before recovering is $L_{ij}(Q) = [(\mathrm{diag}(\gamma) - Q)^{-1}]_{ij}$, so the next-generation matrix and reproduction number are

$$
\Lambda(\pi, Q) = (\mathrm{diag}(\gamma) - Q)^{-1}\mathrm{diag}(\beta)\mathrm{diag}(\pi), \qquad R_0(\pi, Q) = \rho(\Lambda(\pi, Q)).
$$

Let $q_i(\pi, Q)$ be the extinction probability of the branching process started by one infective in group $i$, and $T_{ij}(\pi, Q)$ the number of individuals infected in group $j$ in that process. Define

$$
\omega(\beta,\gamma) = \Big(\sum_{j=1}^m\frac{\gamma_j}{\beta_j}\Big)^{-1}, \qquad \tilde\pi_i = \frac{\gamma_i}{\beta_i}\,\omega(\beta,\gamma).
$$

**Theorem.**
1. *(Reproduction number.)* There is $\tilde Q \in \mathcal{Q}$ with

$$
R_0(\pi, \tilde Q) \ge R_0(\tilde\pi, \tilde Q) = R_0(\tilde\pi, Q) = \omega(\beta,\gamma) \quad \text{for all } \pi, Q,
$$

so $\tilde\pi$ minimises the worst-case reproduction number and $\min_\pi\sup_QR_0 = \omega(\beta,\gamma)$.
2. *(Extinction probability.)* If $\omega(\beta,\gamma) > 1$, then for every $\epsilon > 0$ there is $Q^\epsilon$ with

$$
\min_iq_i(\pi, Q^\epsilon) - \epsilon \le \min_iq_i(\tilde\pi, Q^\epsilon) = \min_iq_i(\tilde\pi, Q) = \omega(\beta,\gamma)^{-1} \quad \text{for all } \pi, Q.
$$

3. *(Expected total size.)* If $\omega(\beta,\gamma) < 1$, then for every $\epsilon > 0$ there is $Q^\epsilon$ with

$$
\max_i\mathbb{E}\Big(\sum_jT_{ij}(\pi, Q^\epsilon)\Big) + \epsilon \ge \max_i\mathbb{E}\Big(\sum_jT_{ij}(\tilde\pi, Q^\epsilon)\Big) = \max_i\mathbb{E}\Big(\sum_jT_{ij}(\tilde\pi, Q)\Big) = (1 - \omega(\beta,\gamma))^{-1}.
$$

Unlike the growth-rate saddle point, no condition on the rates is needed. The same distribution $\tilde\pi \propto \gamma_i/\beta_i$, which places susceptibles where infections are least productive, is optimal for $R_0$, for the worst-case extinction probability above threshold, and for the worst-case expected outbreak size below threshold.

## Depends on

- [Minimax growth rate of a metapopulation epidemic under adversarial migration of infectives](minimax-growth-rate-of-a-metapopulation-epidemic-under-adversarial-migration-of-infectives.md)
- [Branching-process approximation of early epidemics](../../branching-process-approximation-of-early-epidemi/README.md)

## Expansion

At $\tilde\pi$ we have $\beta_i\tilde\pi_i = \omega\gamma_i$, so $\mathrm{diag}(\beta)\mathrm{diag}(\tilde\pi) = \omega\,\mathrm{diag}(\gamma)$. Since $Q\mathbf{1} = 0$, $(\mathrm{diag}(\gamma) - Q)\mathbf{1} = \gamma$ and hence $\Lambda(\tilde\pi, Q)\mathbf{1} = \omega\mathbf{1}$. Thus $R_0(\tilde\pi, Q) = \omega$ for every $Q$. The reverse inequality uses a suitable $\tilde Q$, as in the growth-rate case. For the extinction probabilities, $q$ is the minimal fixed point of the offspring generating function $g(\cdot;\pi,Q)$. Substitution shows $q_i(\tilde\pi, Q) = \omega^{-1}$ for all $i$, and for other $\pi$ a sequence $Q^\epsilon$ with small off-diagonal rates $\delta_i$ gives the bound $\min_iq_i(\pi, Q^\epsilon) \le \min_i(\gamma_i + \delta_i)/(\beta_i\pi_i)$. Since $\sum_i\pi_i = 1$, this cannot exceed $\omega^{-1}$ by more than $\epsilon$. For the total size, $\mathbb{E}\sum_jT_{ij} = [(I - \Lambda)^{-1}\mathbf{1}]_i$ when $R_0 < 1$, and at $\tilde\pi$ this equals $(1-\omega)^{-1}$.

## Sources

- R. McVinish, P. K. Pollett and A. Shausan, "Limiting the spread of disease through altered migration patterns", arXiv:1508.00293 (2015), Section 2.2 (next-generation matrix, Theorems 2.3, 2.4 and 2.5), <https://doi.org/10.48550/arXiv.1508.00293>. Published version: Journal of Theoretical Biology 393 (2016), 60–66, <https://doi.org/10.1016/j.jtbi.2015.12.019>; locators above refer to the arXiv version.
