# Recurrence for generalized Stirling numbers

Let $R$ be a commutative ring and
$s, h \in R$. The generalized Stirling numbers $\mathfrak{S}_{s;h}(n, k) \in R$ are defined by
$\mathfrak{S}_{s;h}(0, 0) = 1$, $\mathfrak{S}_{s;h}(0, k + 1) = \mathfrak{S}_{s;h}(n + 1, 0) = 0$
and the recurrence below. For all natural numbers $n$ and $k$,

$$\mathfrak{S}_{s;h}(n + 1, k + 1) = \mathfrak{S}_{s;h}(n, k) +
h\,(k + 1 + s \max(n - k - 1, 0))\,\mathfrak{S}_{s;h}(n, k + 1).$$

Here $\max(n - k - 1, 0)$ is a natural number viewed as an element of $R$.
