# Final size with gamma-distributed susceptibility and correlated infectiousness

In the [heterogeneous-susceptibility SEIR model](final-size-under-heterogeneous-susceptibility.md), let the susceptibility be gamma distributed with shape $p > 0$ and mean $1$, so $\mathrm{Var}(x) = 1/p$, and let $S(t) = \Phi_0(\bar s(t))$ be the total susceptible fraction, $S_\infty = \lim_{t\to\infty}S(t)$.

**Independent infectiousness.** Here $\mathcal R_0 = \beta/\gamma$ and $S^{-1/p} + \mathcal R_0(S + E + I)$ is conserved, so
$$S_\infty^{-1/p} + \frac{\mathcal R_0}{p}S_\infty = 1 + \frac{\mathcal R_0}{p}.$$

**Correlated infectiousness** ($c(x) = \beta x$). Here $\mathcal R_0 = (1 + 1/p)\beta/\gamma$ and
$$\frac{p+1}{\mathcal R_0}S_\infty^{-1/p} + S_\infty^{1 + 1/p} = 1 + \frac{p+1}{\mathcal R_0}.$$

**Theorem.** Let $\mathcal R_0 > 1$.

1. The independent-case equation has a unique solution $S_\infty(p) \in (0,1)$, and $S_\infty(p)$ is decreasing in $p$.
2. The correlated-case equation has a unique solution $S^*_\infty(p) \in (0,1)$, and $S^*_\infty(p)$ is decreasing in $p$.
3. For the same $\mathcal R_0$ and $p$, $S^*_\infty(p) > S_\infty(p)$: correlation between susceptibility and infectiousness lowers the attack ratio.
4. Compared with the bimodal distribution with the same variance $V$ (susceptibility $V + 1$ with probability $1/(V+1)$, else $0$), whose attack ratio is $(1 - \bar x)/(V+1)$ with $\bar x$ the root in $(0,1)$ of $\log x + \mathcal R_0(1 - x) = 0$, the gamma attack ratio is larger: $(1 - \bar x)/(V+1) < 1 - S_\infty(1/V)$.

So in both cases the final epidemic size decreases as the variance $1/p$ of susceptibility increases.

## Depends on

- [Final size under heterogeneous susceptibility](final-size-under-heterogeneous-susceptibility.md)

## Expansion

For the gamma law $\Phi_0(w) = (1 - \log w/p)^{-p}$ is explicit, so the general final-size equation can be rewritten in the total susceptible fraction, giving the two algebraic equations above. Uniqueness follows as in the general theorem, and monotonicity in $p$ and the comparison of the two cases reduce to elementary inequalities such as $(p+1)x^{1+2/p} - (p+2)x^{1+1/p} + 1 > 0$ on $(0,1)$. In the correlated case the most susceptible hosts are also the most infectious, so they both drive and deplete the epidemic early. Numerically, Beta-distributed susceptibility gives final sizes close to the gamma case with the same variance.

## Sources

- T. Tekeli, A. Pugliese and C. Soresina, "SEIR models with host heterogeneity: theoretical aspects and applications to seasonal influenza dynamics", arXiv preprint (2025), Section 5, Theorems 5.1 and 5.2, Propositions 5.3 and 5.4 and Lemma A.1. <https://doi.org/10.48550/arXiv.2511.18142>