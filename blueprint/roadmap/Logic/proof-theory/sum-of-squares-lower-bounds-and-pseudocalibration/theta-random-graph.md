# Juhász / Feige–Krauthgamer: degree-2 SoS fails for cliques of size o(sqrt n)

For $G \sim G(n, 1/2)$, with high probability the Lovász theta function of the complement satisfies $\vartheta(\overline{G}) = \Theta(\sqrt{n})$; equivalently the degree-$2$ SoS clique relaxation has value $\Theta(\sqrt{n})$. Hence degree-$2$ SoS distinguishes planted cliques of size $k \ge C\sqrt{n}$ but not of size $o(\sqrt{n})$; the same $\Theta(\sqrt{n})$ behaviour persists for a constant number of rounds of the semidefinite Lovász-Schrijver hierarchy $\mathrm{LS}_+$, whose $r$-th round has value $\sqrt{n}/2^{\Theta(r)}$ with high probability.

## Proof sketch

The upper bound uses the spectral norm $\|A - \frac{1}{2}J\| = O(\sqrt{n})$ of the centered adjacency matrix to construct a feasible dual. The lower bound exhibits the primal solution given by the normalized vectors from the adjacency structure, using that $G(n,1/2)$ is pseudorandom.

## Depends on

- [The degree-d SoS relaxation of the clique number](planted-clique-sos-value.md)
- [Lovász theta function](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/lovasz-theta.md)

## Sources

- F. Juhász, "The asymptotic behaviour of Lovász theta function for random graphs", Combinatorica 2 (1982).
- U. Feige, R. Krauthgamer, "The probable value of the Lovász-Schrijver relaxations for maximum independent set", SIAM Journal on Computing 32 (2003) 345-370.
- R. Meka, A. Potechin, A. Wigderson, "Sum-of-squares lower bounds for planted clique", STOC (2015), arXiv:1503.06447, Section 1 (one round of SoS has gap $O(\sqrt{n})$ on $G(n, 1/2)$; $\mathrm{LS}_+(r)$ has gap at most $\sqrt{n}/2^{\Omega(r)}$ and remains $\sqrt{n}/2^r$).
- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A Nearly Tight Sum-of-Squares Lower Bound for the Planted Clique Problem", FOCS (2016), arXiv:1604.03084, Section 1 (degree-$d$ $\mathrm{LS}_+$ recovers the clique only at size at least $\sqrt{n/2^d}$).
- B. Barak, D. Steurer, "Proofs, beliefs, and algorithms through the lens of sum-of-squares", sumofsquares.org, planted clique chapter (Exercise 2: spectral detection of planted cliques of size $C\sqrt{n}$).
- L. Lovász, "Geometric representations of graphs" (2016 course notes), Chapter 6, Section 6.2, Theorem 6.2.1 ($\frac{1}{3}\sqrt{n} < \vartheta(G(n,1/2)) < 3\sqrt{n}$ w.h.p.).
- U. Feige, M. Grinberg, "Upper bounds on the theta function of random graphs", arXiv:2506.02952v1, Section 1.1 (attributes $(\frac{1}{2}-o(1))\sqrt{n} \le \bar{\vartheta}(G(n,1/2)) \le (2+o(1))\sqrt{n}$ to Juhász).
- A. Coja-Oghlan, "The Lovász number of random graphs", arXiv:math/0306266v1 (ECCC TR03-073), Abstract and Section 1.
