# Spectral radius of simple random walk

Let $G$ be a locally finite simple graph with vertex set $V$ and $o \in V$, and let $p_k(o, \cdot)$ be [the recursion of the $k$-step law](walk-prob.md) of simple random walk on $G$ started at $o$. The spectral radius of $G$ seen from $o$ is

$$\rho(G) = \limsup_{n \to \infty} p_{2n}(o, o)^{1/(2n)}.$$

When $o$ has positive degree this is the spectral radius of simple random walk; for vertex-transitive graphs it does not depend on the root $o$. When $o$ is isolated, $p_{2n}(o, o) = 0$ for every $n > 0$ and $\rho(G) = 0$.
