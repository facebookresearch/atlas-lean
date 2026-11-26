# Edge dropping gives a larger major-outbreak probability than increased recovery

In the configuration-model SIR epidemic with infection rate $\beta$, recovery rate $\gamma$ and preventive edge-dropping rate $\omega > 0$ (the $(\gamma, \omega)$ model), compare with the model without dropping and recovery rate $\gamma + \omega$ (the $(\gamma + \omega, 0)$ model). Early in an outbreak, let $Y_k^{(\gamma,\omega)}$ be the number of its $k$ susceptible neighbours that an infective infects, with probability generating function $f_k^{(\gamma,\omega)}$, and similarly $f_k^{(\gamma+\omega)}$. The approximating branching processes have offspring generating function $f(s) = \sum_k p_k f_k(s)$ in the first generation and $\tilde f(s) = \sum_k \tilde p_k f_k(s)$ afterwards, with $\tilde p_k = (k+1) p_{k+1} / \mu_D$.

**Theorem 8.1.** (a) Both models have the same basic reproduction number

$$R_0 = \frac{\beta}{\beta + \gamma + \omega}\left(\mu_D + \frac{\sigma_D^2}{\mu_D} - 1\right).$$

(b) If $R_0 > 1$, the probability of a major outbreak started by one infective, $p_{\mathrm{maj}} = 1 - f(\sigma)$ with $\sigma$ the unique root in $[0, 1)$ of $\tilde f(s) = s$, satisfies

$$p_{\mathrm{maj}}^{(\gamma, \omega)} > p_{\mathrm{maj}}^{(\gamma + \omega, 0)}.$$

## Depends on

- [Reproduction number and final size under preventive edge dropping](reproduction-number-and-final-size-under-edge-dropping.md)

## Expansion

Both models give each edge the same transmission probability $\beta / (\beta + \gamma + \omega)$, so offspring means agree and so does $R_0$. They differ in dependence: with increased recovery, a single recovery time ends transmission to all neighbours at once, making the transmissions of one infective positively correlated; with dropping, the extra "removal" at rate $\omega$ acts independently on each edge. Given equal means, the less correlated offspring distribution is less variable, and for supercritical branching processes a less variable offspring law (in the convex order) has a smaller extinction probability; the paper proves the required ordering $f_k^{(\gamma,\omega)}(s) \le f_k^{(\gamma+\omega)}(s)$ on $[0, 1]$, strict on $[0, 1)$ for $k \ge 2$ (Lemma 1, Equation 8.4), which yields (b).

## Sources

- F. Ball, T. Britton, K. Y. Leung, D. Sirl, "A stochastic SIR network epidemic model with preventive dropping of edges", Journal of Mathematical Biology 78 (2019) 1875–1951, Section 8, Lemma 1, Theorem 8.1, <https://doi.org/10.1007/s00285-019-01329-4> (PMC6469721).
