# Birkhoff averages along the Bernoulli shift are empirical means

Let $S$ be a set, $\sigma$ the [left shift](../mixing/shift.md) on $S^{\mathbb{N}}$ and
$g : S \to \mathbb{R}$. For every $n \ge 0$ and every sequence $x = (x_0, x_1, \dots) \in S^{\mathbb{N}}$, the $n$-th
Birkhoff average of the function $y \mapsto g(y_0)$ along $\sigma$ at $x$ is the empirical mean

$$\frac{1}{n} \sum_{k=0}^{n-1} g\bigl((\sigma^k x)_0\bigr) = \frac{1}{n} \sum_{k=0}^{n-1} g(x_k),$$

where both sides are $0$ for $n = 0$.
