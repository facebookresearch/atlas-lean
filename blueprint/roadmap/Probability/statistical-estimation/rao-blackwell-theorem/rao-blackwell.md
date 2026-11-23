# The Rao–Blackwell theorem

Let $(\Omega, \mathcal{F})$ be a measurable space, $(P_\theta)_{\theta \in \Theta}$ probability measures on it, and $\mathcal{G} \subseteq \mathcal{F}$ a sub-σ-algebra [sufficient](../sufficient-statistics-and-the-factorization-theo/is-sufficient.md) for $(P_\theta)$. Let $W$ be an $\mathcal{F}$-measurable real estimator, integrable under every $P_\theta$. Then there is one parameter-free $\mathcal{G}$-measurable estimator $\eta$ such that for every $\theta$:

- $\eta = \mathbb{E}_{P_\theta}[W \mid \mathcal{G}]$ $P_\theta$-almost everywhere;
- $\mathbb{E}_{P_\theta}\eta = \mathbb{E}_{P_\theta} W$;
- for every loss $\ell_\theta : \mathbb{R} \to \mathbb{R}$ convex in the estimate with $\ell_\theta(W)$ $P_\theta$-integrable, $\mathbb{E}_{P_\theta}\, \ell_\theta(\eta) \le \mathbb{E}_{P_\theta}\, \ell_\theta(W)$.

## Sources

- C. R. Rao, *Information and the accuracy attainable in the estimation of statistical parameters*, Bull. Calcutta Math. Soc. 37 (1945), 81–91.
- D. Blackwell, *Conditional expectation and unbiased sequential estimation*, Ann. Math. Statist. 18 (1947), 105–110.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, Section 7.3.
