# Ramanujan graph (spectral radius of the regular tree)

Let $G$ be a simple graph, $d \in \mathbb{N}$ and $o$ a vertex, and let $W_n(o, o)$ be the [number of closed walks](walk-count.md) of length $n$ at $o$, read as $0$ when there are infinitely many. Then $G$ is Ramanujan of degree $d$ (seen from $o$) if

$$\limsup_{n \to \infty} \Big( \frac{W_n(o, o)}{d^n} \Big)^{1/n} = \frac{2\sqrt{d - 1}}{d},$$

with division by zero read as $0$ and $\sqrt{x} = 0$ for $x < 0$. The definition is this equality alone; it does not require $G$ to be regular. For $d \ge 2$ the right side is the spectral radius of the $d$-regular tree, and if moreover $G$ is $d$-regular, $W_n(o, o)/d^n$ is the probability that simple random walk from $o$ is back at $o$ at time $n$. The comparison fails for small $d$: for $d = 1$ the right side is $0$, while the one-edge $1$-regular tree has even-time return probability $1$ and spectral radius $1$; for $d = 0$ both sides are computed with division by zero and the ratios vanish at every positive $n$.
