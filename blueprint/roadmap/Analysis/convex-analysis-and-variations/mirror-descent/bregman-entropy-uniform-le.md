# The $\omega$-diameter of the simplex under the entropy is at most $\log n$

For $n \ge 1$ and every $u$ in the [simplex](simplex.md), $V_{c}(u) \le \log n$, where $c$ is the [uniform point](uniform.md), the minimizer of the [entropy](entropy.md). Since $V_c(u) = \sum_i u_i \log(n u_i)$ and $n u_i \le n$, each term is at most $u_i \log n$. The bound is attained at the vertices. Combined with [strong convexity](bregman-entropy-ge.md) it makes the mirror descent rate depend on the dimension only through $\sqrt{\log n}$.

## Sources

- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, Example: $D_{\omega,X} = \sqrt{\ln n}$ and $x_1 = n^{-1}(1, \ldots, 1)^T$.
