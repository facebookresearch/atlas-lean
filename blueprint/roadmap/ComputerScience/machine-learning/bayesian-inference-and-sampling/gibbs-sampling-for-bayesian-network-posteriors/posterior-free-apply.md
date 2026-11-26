# Posterior of the free variables as a ratio

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a finite nonempty type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. Let $E \subseteq \{0, \dots, n-1\}$ be a set of evidence nodes with evidence values $e$; the free (non-evidence) variables are the configurations $z$ of the nodes outside $E$, and $(e, z)$ denotes the full assignment that equals $e$ on $E$ and $z$ off $E$. Write $P(e) = \sum_{x : x|_E = e|_E} P(x)$ for the evidence probability.

If $P(e) \ne 0$, then for every configuration $z$ of the free variables the posterior of the free variables satisfies

$$P(z \mid X_E = e) = \frac{P\big((e, z)\big)}{P(e)} ,$$

as an element of $[0, \infty]$ (the real ratio mapped into the extended nonnegative reals).
