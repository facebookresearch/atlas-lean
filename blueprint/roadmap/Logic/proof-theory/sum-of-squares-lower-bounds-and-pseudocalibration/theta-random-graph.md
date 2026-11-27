# Juhász / Feige–Krauthgamer: degree-2 SoS fails for cliques of size o(sqrt n)

For $G \sim G(n, 1/2)$, with high probability the Lovász theta function of the complement satisfies $\vartheta(\overline{G}) = \Theta(\sqrt{n})$; equivalently the degree-$2$ SoS clique relaxation has value $\Theta(\sqrt{n})$. Hence degree-$2$ SoS distinguishes planted cliques of size $k \ge C\sqrt{n}$ but not of size $o(\sqrt{n})$; the same $\Theta(\sqrt{n})$ behaviour persists for a constant number of rounds of the semidefinite Lovász-Schrijver hierarchy $\mathrm{LS}_+$, whose $r$-th round has value $\Theta(\sqrt{n/2^r})$ with high probability.

## Proof sketch

The upper bound uses the spectral norm $\|A - \frac{1}{2}J\| = O(\sqrt{n})$ of the centered adjacency matrix to construct a feasible dual. The lower bound exhibits the primal solution given by the normalized vectors from the adjacency structure, using that $G(n,1/2)$ is pseudorandom.

## Depends on

- [The degree-d SoS relaxation of the clique number](planted-clique-sos-value.md)
- [Lovász theta function](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/lovasz-theta.md)

## Sources

- F. Juhász, "The asymptotic behaviour of Lovász theta function for random graphs", Combinatorica 2 (1982) 153-155.
- U. Feige, R. Krauthgamer, "The probable value of the Lovász-Schrijver relaxations for maximum independent set", SIAM Journal on Computing 32 (2003) 345-370.
