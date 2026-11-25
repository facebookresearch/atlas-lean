# Logistic regression is the Bernoulli GLM

For data $(X_k, Y_k)_{k < m}$ with features $X_k \in \mathbb{R}^\iota$, for a finite index set $\iota$, and Boolean labels $Y_k$, and for every weight vector $w$, the empirical risk of logistic regression equals the generalized linear model loss with log-partition the softplus function $z \mapsto \log(1 + e^z)$ and responses the label indicators $[Y_k = \text{true}]$.
