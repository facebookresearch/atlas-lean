# The reweighted mass along a hypothesis

Let $D$ be weights on the $m$ training points with $\sum_i D_i = 1$, let $h$ be a hypothesis with weighted error $\varepsilon = \sum_{i : h(x_i) \ne y_i} D_i$, and let $a \in \mathbb{R}$. Then

$$\sum_i D_i\, e^{-a y_i h(x_i)} = (1 - \varepsilon) e^{-a} + \varepsilon e^{a}.$$

This is the one-dimensional function that AdaBoost minimizes when it chooses $\alpha_t$; its minimum over $a$ is $2\sqrt{\varepsilon(1-\varepsilon)}$, attained at $a = \tfrac12 \log((1-\varepsilon)/\varepsilon)$.

## Sources

- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the margin: a new explanation for the effectiveness of voting methods", *Ann. Statist.* 26 (1998), 1651–1686, the computation of $Z_t$ preceding Theorem 5.
