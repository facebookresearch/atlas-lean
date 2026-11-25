# Per cell control

Let $(\Omega, \mu)$ be a probability space, $T \subseteq \Omega$ a measurable treatment event, $\mathcal{X}$ a measurable space with measurable singletons, $X : \Omega \to \mathcal{X}$ a measurable covariate, and $Y_0, Y_1 : \Omega \to \mathbb{R}$ potential outcomes with observed outcome $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$. Write $\mu(\cdot \mid A) = \mu(A)^{-1}\, \mu(\cdot \cap A)$ denotes the conditional measure (the zero measure when $\mu(A) = 0$). Suppose $Y_0$ is measurable and integrable. Assume strong ignorability of $T$ for $Y_0$ given $X$: for every measurable $B \subseteq \mathbb{R}$ and every $x$, $\mu(T, Y_0 \in B, X = x)\, \mu(X = x) = \mu(T, X = x)\, \mu(Y_0 \in B, X = x)$, and for every $x$ with $\mu(X = x) \neq 0$ the propensity $e(x) = \mu(T \cap \{X = x\}) / \mu(X = x)$ satisfies $0 < e(x) < 1$. Then for every $x \in \mathcal{X}$,

$$\mu(X = x) \int Y \, d\mu(\cdot \mid T^c \cap \{X = x\}) = \int_{\{X = x\}} Y_0 \, d\mu.$$
