# Dominant sets determine Boolean network attractors

**Setting.** A Boolean network on a finite directed graph $(V,A)$ is a map $F:\{0,1\}^V\to\{0,1\}^V$ whose coordinate $v$ depends only on the in-neighbours $I(v)$ of $v$. A set $U\subset V$ is *dominant* if, starting from $U_0=U$ and repeatedly adding every vertex all of whose inputs already lie in the current set, one reaches $U_d=V$ after finitely many steps; the minimal such $d=d(U)$ is the *depth*. The reduced graph on $U$ has an arc $u'\to u$ whenever a simple path in $(V,A)$ leads from $u'$ to $u$, and the *recurrence length* $\ell(U)$ is the maximal length of such paths (so $\ell\le d+1$).

**Theorem.**

1. $U$ is dominant if and only if every directed cycle of $(V,A)$ contains a vertex of $U$ (i.e. $U$ is a feedback vertex set).
2. If two orbits agree on $U$ for $d(U)+1$ consecutive times, $F^t(x)_U = F^t(y)_U$ for $t_0\le t\le t_0+d(U)$, then $F^t(x)=F^t(y)$ for all $t\ge t_0+d(U)$.
3. With $\ell=\ell(U)$, the map $\theta(x) = \big(F^{\ell-1}(x)_U, \dots, F(x)_U, x_U\big)\in(\{0,1\}^U)^{\ell}$ satisfies $\hat F\circ\theta = \theta\circ F$ for an automata network $\hat F$ on $(\{0,1\}^U)^\ell$ induced by $U$, and $\theta$ is injective on the periodic points of $F$. Hence the attractors of $F$ (fixed points and limit cycles, with their periods) correspond one-to-one to those of the reduced system on the dominant set.

## Expansion

Removing a vertex set that meets every cycle leaves an acyclic graph, whose vertices can be ordered so that each is a function of earlier ones and of $U$; this is the depth chain, and it shows that the values on $U$ over a window of length $d+1$ determine the whole state. Recording the last $\ell$ values on $U$ captures all delayed influences along simple paths between dominant vertices, which gives the semiconjugacy; on the eventually periodic part of the dynamics the state is recovered from this history, so attractors are preserved. For gene regulatory networks this reduces attractor search to the (typically small) set of vertices on feedback loops.

## Sources

- A. España, W. Funez, E. Ugalde, "Dominant vertices and attractors' landscape for Boolean networks", *Discrete and Continuous Dynamical Systems - B* 37 (2026), 254–274, Proposition 1, Theorems 1–2 and Corollary 1, <https://doi.org/10.3934/dcdsb.2026051> (preprint arXiv:2509.03654).
