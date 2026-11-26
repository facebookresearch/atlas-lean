# Bayes-factor adjustment of the null proportion in functional adaptive shrinkage

**Setting (dynamic eQTLs).** For each variant–gene unit $j = 1,\dots,J$, the genetic effect on expression is a function $\beta_j(t)$ of a continuous condition $t \in \Omega$ (such as differentiation time). It is observed as noisy estimates $\hat{\boldsymbol\beta}_j$ with standard errors $\boldsymbol s_j$. Fix a $p$th-order linear differential operator $L$ (for example $L = D^p$). The **baseline model** is $S_0 = \{\beta : L\beta = 0\}$, so $L = D^1$ gives constant (static) effects. An $L$-Gaussian process with scale $\sigma$ solves $L\beta = \sigma \xi$ for white noise $\xi$; for $L = D^p$ it is the $p$th-order integrated Wiener process. **Functional adaptive shrinkage** places on each $\beta_j$ the mixture prior

$$
g_\beta = \sum_{k=0}^K \pi_k\, L\text{-GP}(\beta; \sigma_k), \qquad 0 = \sigma_0 < \sigma_1 < \dots < \sigma_K,
$$

estimates the weights $\pi_k$ by marginal likelihood, and treats the component $\sigma_0 = 0$ (no deviation from $S_0$) as the null hypothesis $H_0$, i.e. no dynamic effect.

**Lemma (Bayes factors are e-values).** If $\mathrm{BF}_j = p_1(\hat{\boldsymbol\beta}_j \mid \boldsymbol s_j)/p_0(\hat{\boldsymbol\beta}_j \mid \boldsymbol s_j)$, then $\mathbb{E}_0(\mathrm{BF}_j) = 1$ under $H_0$, whatever alternative marginal $p_1$ is used.

**Adjustment.** Collapse the fitted alternative components into one marginal likelihood, compute $\mathrm{BF}_j$, and for cutoffs $c$ let $\hat\pi_0(c) = J_0(c)/J$ with $J_0(c) = \#\{j : \mathrm{BF}_j < c\}$ and $\mu(c)$ the mean Bayes factor among those units. Set $c^* = \inf\{c : \mu(c) \ge 1 + \epsilon\}$ and $\hat\pi_0 = \hat\pi_0(c^*)$, rescaling the alternative weights to sum to $1 - \hat\pi_0$.

**Theorem.** If the $J_0$ null effects are i.i.d. from the null distribution specified by the prior, then for any specification of the alternative components and any buffer $\epsilon > 0$,

$$
\hat\pi_0 \ge \pi_0 = J_0/J \quad \text{almost surely as } J_0 \to \infty.
$$

Moreover, if $\tilde\pi_0 \ge \pi_0$ then the posterior odds of a dynamic effect computed with $\tilde\pi_0$ are conservative: $\mathbb{E}_{H_0}[\widetilde{\mathrm{PO}}] \le \mathbb{E}_{H_0}[\mathrm{PO}]$ and $\mathbb{E}_{H_1}[\log \widetilde{\mathrm{PO}}] \le \mathbb{E}_{H_1}[\log \mathrm{PO}]$.

## Expansion

$\mathbb{E}_0(\mathrm{BF}_j) = \int p_1 = 1$. By the strong law of large numbers, the average Bayes factor over the true nulls tends to $1$, so any set of units whose average Bayes factor stays at or below $1$ can, asymptotically, contain all nulls only if it is at least as large as $\mathcal{H}_0$. The procedure picks the largest set of smallest Bayes factors whose mean stays below $1 + \epsilon$. That set eventually contains every null unit, so its size overestimates $J_0$. Over-estimating $\pi_0$ protects local false sign rates and FDR against misspecification of the high-dimensional mixture prior, which otherwise tends to under-estimate $\pi_0$.

## Sources

- Ziang Zhang, Peter Carbonetto, Matthew Stephens, "Empirical Bayes Shrinkage of Functional Effects, with Application to Analysis of Dynamic eQTLs", arXiv (2026). Section 3, Lemma 1, Algorithm 1, Theorem 1; Appendix B, Theorem 2, Lemma 2, Lemma 3. <https://doi.org/10.48550/arXiv.2602.03077>
