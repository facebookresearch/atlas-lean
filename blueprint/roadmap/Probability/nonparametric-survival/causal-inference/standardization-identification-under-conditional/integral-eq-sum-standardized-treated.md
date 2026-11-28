# Standardization, treated arm

Let $\mu$ be a probability measure, $T$ a measurable treatment event, $X$ a measurable covariate with values in a finite measurable space with measurable singletons (so every fibre $\{X = x\}$ is an event), and $Y_1$ a measurable integrable treated potential outcome. Assume strong ignorability: $T \perp Y_1 \mid X$ and $0 < P(T \mid X = x) < 1$ for every $x$ with $P(X = x) > 0$. With the observed outcome $Y = Y_1$ on $T$ and $Y = Y_0$ off $T$, $E[Y_1] = \sum_x P(X = x)\,E[Y \mid T, X = x]$, where terms with $P(X = x) = 0$ contribute $0$.
