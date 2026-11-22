# Conditional law of a Gaussian process at one time given another

Let $X = (X_t)_{t \in T}$ be a real Gaussian process with measurable coordinates and $\mathbb E X_t = 0$ for every
$t$, let $s, t \in T$, and let $c$ be a real number with $\operatorname{Cov}(X_s, X_t) = c \operatorname{Var}(X_s)$.
Then for almost every $x$ (with respect to the law of $X_s$), the conditional law of $X_t$ given $X_s = x$ is
$N\bigl(c x,\ \operatorname{Var}(X_t) - c^2 \operatorname{Var}(X_s)\bigr)$, the variance being truncated at $0$.
