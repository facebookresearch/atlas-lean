# Identification of the ATE by standardization

Let $\mu$ be a probability measure, $T$ a measurable treatment event, $X$ a measurable covariate with finitely many values, and $Y_0$, $Y_1$ measurable integrable potential outcomes. Assume strong ignorability: $T$ is conditionally independent of $(Y_0, Y_1)$ given $X$, and $0 < P(T \mid X = x) < 1$ for every $x$ with $P(X = x) > 0$. Let $Y$ be the observed outcome, $Y_1$ on $T$ and $Y_0$ off $T$. Then

$$\mathbb E[Y_1 - Y_0] = \sum_x P(X = x)\left(\mathbb E[Y \mid T, X = x] - \mathbb E[Y \mid T^c, X = x]\right).$$
