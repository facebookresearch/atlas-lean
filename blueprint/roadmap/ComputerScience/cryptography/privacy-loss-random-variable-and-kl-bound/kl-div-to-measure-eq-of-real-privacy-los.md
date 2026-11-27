# Kullback–Leibler divergence equals the expected privacy loss

Let $\Omega$ be a countable measurable space with measurable singletons, $P, Q$ probability mass functions on $\Omega$ and $\varepsilon \ge 0$, with $P(w) \le e^{\varepsilon} Q(w)$ and $Q(w) \le e^{\varepsilon} P(w)$ for every $w$. Then the Kullback–Leibler divergence of the induced measures, a value in $[0, \infty]$, equals the [expected privacy loss](privacy-loss-expectation.md):

$$
\mathrm{KL}(P \,\|\, Q) = \sum_w P(w)\, L_{P\|Q}(w).
$$
