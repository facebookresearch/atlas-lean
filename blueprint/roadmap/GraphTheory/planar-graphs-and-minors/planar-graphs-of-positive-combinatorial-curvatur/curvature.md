# Combinatorial curvature at a vertex

Let $G$ be a simple graph on a finite vertex set $V$, with darts (ordered pairs $(u, v)$ of adjacent vertices) and a permutation $\rho$ of the darts. The combinatorial curvature at a vertex $v$ is the rational number

$$1 - \frac{\deg v}{2} + \sum_{d} \frac{1}{|f(d)|},$$

the sum over the darts $d$ at $v$ (one term for each corner at $v$), where $|f(d)|$ is the size of the face through $d$ under the face permutation $\varphi(u, v) = \rho(v, u)$ and $\deg v$ is the number of darts at $v$.

The words face, corner and facial walk describe an embedding only when $\rho$ is a [rotation system](is-rotation-system.md); for an arbitrary permutation $\rho$ the quantities here are orbit counts of the face permutation.
