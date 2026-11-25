# Elementary lower bound on the spectral parameter

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector. If $N \ge 2$, then

$$d\,(N - d) \le (d\lambda)^2\, (N - 1);$$

for $d \ge 1$ this says $\lambda \ge \sqrt{(N - d)/(d(N - 1))}$, which tends to $1/\sqrt d$ as $N \to \infty$ with $d$ fixed. The test vector is $e_v - \frac1N \mathbf 1$ for any vertex $v$. This is the trivial bound $1/\sqrt D - o(1)$ mentioned in S. Vadhan, *Pseudorandomness* (2012), Section 4.1.3, before Theorem 4.11 (the Alon–Boppana bound $2\sqrt{D-1}/D - o(1)$ improves it).

## Background

- [Alon-Boppana bound](alon-boppana.md): the sharp asymptotic lower bound $2\sqrt{d - 1}/d - o(1)$,
  which improves this one by a factor of about $2$ for large $d$.
- [The complete graph is a spectral expander](is-spectral-expander-top.md): the complete graph
  attains this bound with equality.
