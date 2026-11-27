# The flow Poincaré inequality

If every elongated edge load of a [multicommodity flow](multicommodity-flow.md) is at most $B\,\pi(u)P(u,v)$, then for every $\psi$,
$\sum_{x,y} (\psi(x)-\psi(y))^2\pi(x)\pi(y) \le B\sum_{x,y}(\psi(x)-\psi(y))^2\pi(x)P(x,y)$.
Sinclair notes that the proof of Theorem 5 "carries over almost unchanged" (A. Sinclair, *Combinatorics, Probability and Computing* 1 (1992), Section 4): split $\pi(x)\pi(y)$ over the paths of commodity $(x,y)$ and apply the canonical-path argument to each path.
