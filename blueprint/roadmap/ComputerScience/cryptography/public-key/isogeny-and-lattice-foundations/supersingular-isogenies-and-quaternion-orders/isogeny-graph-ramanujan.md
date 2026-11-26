# Supersingular isogeny graphs are Ramanujan and random walks mix rapidly

Let $\ell\ne p$ be primes, and let $\mathcal{G}_\ell(p)$ have as vertices the isomorphism classes of supersingular elliptic curves over $\mathbb{F}_{p^{2}}$ and, from each $E$, one edge for each of its $\ell+1$ subgroups of order $\ell$, to the corresponding quotient curve. Its adjacency matrix is the Brandt matrix $B(\ell)$, which is not symmetric when some curve has $\#\mathrm{Aut}(E)>2$, but every eigenvalue $\lambda$ of $B(\ell)$ other than the trivial eigenvalue $\ell+1$ satisfies $|\lambda|\le2\sqrt{\ell}$. Consequently, the random walk that at each step quotients by a uniformly random subgroup of order $\ell$ converges to the stationary distribution $f(E)=24/\bigl((p-1)\,\#\mathrm{Aut}(E)\bigr)$, not in general to the uniform distribution: for every $\varepsilon>0$ there is $n=O(\log_\ell p-\log_\ell\varepsilon)$ such that the endpoint of a walk of length at least $n$ from any vertex is within statistical distance $\varepsilon$ of $f$. The distribution $f$ is within statistical distance $O(1/p)$ of uniform, rejection sampling turns samples from $f$ into uniform samples, and $f$ is uniform when every curve has $\mathrm{Aut}(E)=\{\pm1\}$. The non-backtracking walk, which never takes the dual of the previous step, is a different Markov chain, on directed edges, and is not covered by this statement.

## Proof sketch

The adjacency operator is identified, via the Deuring correspondence, with the Brandt matrix of $B_{p,\infty}$ at $\ell$, i.e., a Hecke operator on weight-$2$ modular forms of level $p$; Deligne's proof of the Ramanujan–Petersson conjecture bounds its nontrivial eigenvalues by $2\sqrt{\ell}$. Dual isogenies give a bijection between degree-$\ell$ isogenies $E\to E'$ and $E'\to E$, and an edge counts such isogenies up to automorphisms of the target, so $\#\mathrm{Aut}(E')\,B(\ell)_{E,E'}=\#\mathrm{Aut}(E)\,B(\ell)_{E',E}$. The walk is therefore reversible with respect to weights proportional to $1/\#\mathrm{Aut}(E)$, whose total is $(p-1)/24$ by the Eichler mass formula, and the spectral bound for a reversible chain gives the mixing time to $f$.

## Depends on

- [Supersingular l-isogeny graphs](supersingular-isogeny-graph.md)

## Proof depends on

- [The Deuring correspondence between supersingular curves and maximal orders](deuring-correspondence.md)

## Sources

- Arnold K. Pizer, "Ramanujan Graphs and Hecke Operators", Bulletin of the AMS (1990).
- Denis X. Charles, Kristin E. Lauter, Eyal Z. Goren, "Cryptographic Hash Functions from Expander Graphs", Journal of Cryptology (2009).
- Aurel Page, Benjamin Wesolowski, "The Supersingular Endomorphism Ring and One Endomorphism Problems Are Equivalent", EUROCRYPT (2024), Proposition 2.7, arXiv:2309.10432.
