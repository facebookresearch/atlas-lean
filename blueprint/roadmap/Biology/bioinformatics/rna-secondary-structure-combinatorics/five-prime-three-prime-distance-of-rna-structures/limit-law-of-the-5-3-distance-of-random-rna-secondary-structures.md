# Limit law of the 5'–3' distance of random RNA secondary structures

**Setting.** An RNA secondary structure of length $n$ is a diagram on vertices $1,\dots,n$ with backbone edges $(i,i+1)$ and a set of non-crossing arcs (base pairs) in the upper half-plane, each vertex in at most one arc, with no arcs of the form $(i,i+1)$. Its *5'–3' distance* is the length of a shortest path from vertex $1$ to vertex $n$ using backbone edges and arcs. Let $w(n,d)$ be the number of structures of length $n$ with distance $d$, $w(n)=\sum_d w(n,d)$, and let

$$S(z)=\frac{1-z+z^2-\sqrt{(z^2+z+1)(z^2-3z+1)}}{2z^2}$$

be the generating function of secondary structures by length.

**Theorem.**

1. The bivariate generating function $W(z,u)=\sum_{n,d}w(n,d)z^nu^d$ is

$$W(z,u)=\frac{u z^2\,(S(z)-1)}{(1-zu)^2-(1-zu)(zu)^2\,(S(z)-1)}+\frac{z}{1-zu}.$$

2. For every $d\ge1$, $\lim_{n\to\infty}w(n,d)/w(n)=q(d)$, where the limit law has the probability generating function $Q(u)=\sum_d q(d)u^d=m_1(u)/m_2(u)$ with

$$m_1(u)=(-7+3\sqrt5)\,u,\qquad m_2(u)=-2-2(-3+\sqrt5)u+(-15+7\sqrt5)u^2+(22-10\sqrt5)u^3+2(-9+4\sqrt5)u^4.$$

3. With $\delta=\tfrac14\big(-1-\sqrt5+\sqrt{38+18\sqrt5}\big)\approx1.40$, the limit law has the tail

$$q(d)\sim\frac{C}{\delta}\,(d+1)\,\delta^{-(d+1)},$$

the shape of a discretized $\Gamma(\ln\delta,2)$ density, for a constant $C>0$. In particular the 5'–3' distance of a random structure stays bounded in probability as $n\to\infty$: the two ends of a long random RNA are close in the structure, as observed empirically for real RNAs.

An analogous closed form holds for $r$-canonical structures (every helix has at least $r$ base pairs), with $z^2$ replaced by $z^{2r}$, $S$ by the generating function $S_r$ of $r$-canonical structures, and an extra factor $1-z^2+z^{2r}$ in the denominator.

## Expansion

Secondary structures correspond bijectively to sequences of $1$-tableaux (lattice walks recording open arcs), and the 5'–3' distance is read off from the outermost level: a shortest path walks along the backbone between exterior arcs and jumps over each exterior arc. Decomposing a structure into a sequence of exterior blocks (isolated exterior vertices, or an exterior arc enclosing an arbitrary structure) gives a geometric series in $zu$ and $S(z)$, which yields $W(z,u)$. The dominant singularity $\rho=(3-\sqrt5)/2$ of $S$ is a square-root singularity not affected by $u$ near $1$, so a singular expansion of $W(z,u)$ at $\rho$ and the transfer theorem give $w(n,d)/w(n)$ converging pointwise in $u$ to the rational function $Q(u)$; a continuity theorem for probability generating functions converts this into convergence of each $q(d)$. The tail comes from the double pole of $Q$ at $u=\delta$.

## Sources

- Hillary S. W. Han, Christian M. Reidys, "The 5'-3' distance of RNA secondary structures", arXiv:1104.3316 (2011): Section 2 (diagrams, distance, tableaux bijection), Section 3 (exact bivariate generating function theorem), Section 4 (singular expansion and transfer theorem), Section 5 (continuity theorem, limit theorem with $m_1,m_2$, Gamma-tail corollary), Section 6 (the $r$-canonical generating function). <https://doi.org/10.48550/arXiv.1104.3316> Published version: Journal of Computational Biology 19 (2012) 867–878, <https://doi.org/10.1089/cmb.2011.0301>.
