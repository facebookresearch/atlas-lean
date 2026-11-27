# Truncated signature series of a linear controlled equation

Let $\iota$ be finite, let $E$ be a real normed space, let $(A_i)_{i \in \iota}$ be bounded linear maps $E \to E$ with [composites](word-op.md) $A_w$, let $X$ be a path with velocity $v$, and let $s \in \mathbb{R}$ and $y_0 \in E$. The truncated signature series of degree $n$ at time $t$ is

$$
y^{(n)}_t = \sum_{k=0}^{n} \sum_{|w| = k} S(X)^w_{s,t}\, A_w\, y_0,
$$

a formal degree-$n$ truncation of the signature expansion, defined for an arbitrary velocity through the [iterated integrals](signature.md) (with their integral convention). When $E$ is a Banach space and the components of $v$ are continuous, it is the degree-$n$ truncation of the series solving $dy = \sum_i A_i\, y\, dX^i$, $y_s = y_0$ (T. Lyons, Proc. ICM 2014, arXiv:1405.4537, §4.2, equation (1), for a Banach state space and a smooth control).
