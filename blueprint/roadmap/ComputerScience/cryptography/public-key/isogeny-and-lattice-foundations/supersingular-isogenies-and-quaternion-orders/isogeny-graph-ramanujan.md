# Supersingular isogeny graphs are Ramanujan and random walks mix rapidly

For primes $\ell\ne p$, every eigenvalue $\lambda$ of the adjacency operator of $\mathcal{G}_\ell(p)$ other than the trivial eigenvalue $\ell+1$ satisfies $|\lambda|\le 2\sqrt{\ell}$. Consequently, for a non-backtracking or simple random walk of length $k$ from any vertex, the distribution of the endpoint is within statistical distance $\sqrt{n}\,(2\sqrt{\ell}/(\ell+1))^{k}$ of uniform (stationary) on the $n\approx p/12$ vertices, so walks of length $O(\log p)$ reach an essentially uniform supersingular curve.

## Proof sketch

The adjacency operator is identified, via the Deuring correspondence, with the Brandt matrix of $B_{p,\infty}$ at $\ell$, i.e., a Hecke operator on weight-$2$ modular forms of level $p$; Deligne's proof of the Ramanujan–Petersson conjecture bounds its nontrivial eigenvalues by $2\sqrt{\ell}$. The mixing bound is the standard spectral estimate for regular graphs.

## Depends on

- [Supersingular l-isogeny graphs](supersingular-isogeny-graph.md)
- [The Deuring correspondence between supersingular curves and maximal orders](deuring-correspondence.md)

## Proof depends on

- [Supersingular l-isogeny graphs](supersingular-isogeny-graph.md)
- [The Deuring correspondence between supersingular curves and maximal orders](deuring-correspondence.md)

## Sources

- Arnold K. Pizer, "Ramanujan Graphs and Hecke Operators", Bulletin of the AMS (1990).
- Denis X. Charles, Kristin E. Lauter, Eyal Z. Goren, "Cryptographic Hash Functions from Expander Graphs", Journal of Cryptology (2009).
