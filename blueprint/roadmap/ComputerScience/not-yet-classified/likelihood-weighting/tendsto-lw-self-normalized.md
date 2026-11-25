# Self-normalized likelihood weighting is consistent

Let $b$ be a Bayesian network on $n$ variables over a finite nonempty alphabet, $E$ a set of evidence nodes with evidence $e$ of positive probability, and $f$ a real function of full assignments. Let $X_1, X_2, \dots$ be measurable, pairwise independent samples, each with the law of the network with the evidence nodes clamped to $e$. With likelihood weights $w(x) = \prod_{k \in E} p_k(x_k \mid x_{\mathrm{pa}(k)})$, the estimate

$$\frac{\sum_{i<m} w(X_i)\,f(X_i)}{\sum_{i<m} w(X_i)}$$

converges almost surely to $\mathbb E[f \mid X_E = e]$.
