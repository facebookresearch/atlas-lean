# Low-noise linear regulatory networks have no unexpected correlations

**Model.** Let $G = (V, E)$ be a finite directed acyclic graph with a single root $o$ and real edge weights $c_{uv}$. Gene expression levels satisfy the linear structural equations

$$M_v = \sum_{u \in \mathrm{pa}(v)} c_{uv} M_u + \varepsilon_v, \qquad v \ne o,$$

with mutually independent noise $\varepsilon_v$ of mean $0$ and variance $\sigma_v^2$. An *equilibrium state* is the joint law obtained by fixing the law of the root variable; two states $P$ and $Q$ (for example disease and control) use independent root variables $M_o^{(P)}, M_o^{(Q)}$ and independent copies of the noise. Write $\Delta_v = \mathbb{E} M_v^{(P)} - \mathbb{E} M_v^{(Q)}$. An edge between $v$ and $w$ of a co-expression network is an *expected link* if

$$\Delta_v \Delta_w \operatorname{cov}\bigl(M_v^{(P)}, M_w^{(P)}\bigr) > 0 \quad \text{and} \quad \Delta_v \Delta_w \operatorname{cov}\bigl(M_v^{(Q)}, M_w^{(Q)}\bigr) > 0,$$

i.e. the sign of the within-state correlation agrees with the direction of differential expression, and an *unexpected link* otherwise.

**Claim.** Let $a_v = \sum_{\text{paths } o \to v} \prod_{\text{edges}} c$ be the total path coefficient, so that $M_v = a_v M_o + (\text{noise terms})$. Assume $\mathbb{E} M_o^{(P)} \ne \mathbb{E} M_o^{(Q)}$ and $\operatorname{Var} M_o^{(P)}, \operatorname{Var} M_o^{(Q)} > 0$. Then there is $\sigma_0 > 0$ such that, if $\sigma_v^2 < \sigma_0^2$ for every $v$, every pair of genes $v, w$ with $a_v a_w \ne 0$ is an expected link. Thus, in this regime, unexpected links arise only from noise (or from genes with no net dependence on the regulator), and the proportion of unexpected correlations (PUC) measures network error.

**Error estimate.** Arguing that a false edge is about equally likely to be expected or unexpected, the source estimates the proportion of false links in a thresholded co-expression network as twice the observed proportion of unexpected links, and removes the unexpected links, roughly halving the number of false edges.

## Expansion

Solving the structural equations in topological order gives $M_v = a_v M_o + \eta_v$, where $\eta_v$ is a linear combination of the noise variables, independent of $M_o$, with variance $O(\max_u \sigma_u^2)$. Then $\Delta_v = a_v \Delta_o$ and $\operatorname{cov}(M_v, M_w) = a_v a_w \operatorname{Var}(M_o) + \operatorname{cov}(\eta_v, \eta_w)$ in each state, so

$$\Delta_v \Delta_w \operatorname{cov}(M_v, M_w) = a_v^2 a_w^2 \Delta_o^2 \operatorname{Var}(M_o) + a_v a_w \Delta_o^2 \operatorname{cov}(\eta_v, \eta_w).$$

The first term is strictly positive under the hypotheses, and the second is bounded by a constant times $\max_u \sigma_u^2$ by Cauchy–Schwarz, so it is dominated once the noise is small enough; finiteness of $V$ makes $\sigma_0$ uniform over pairs. The source states the lemma for linear models, notes that the same sign argument extends to monotone structural relations, and proves the general multi-root case and the factor-two error estimate in its supplementary material.

## Sources

- A. Yambartsev, M. A. Perlin, Y. Kovchegov, N. Shulzhenko, K. L. Mine, X. Dong and A. Morgun, "Unexpected links reflect the noise in networks", Biology Direct 11 (2016), 52, Eq. (1), Definition and Lemma 1. <https://doi.org/10.1186/s13062-016-0155-0> PMCID: PMC5480421.
