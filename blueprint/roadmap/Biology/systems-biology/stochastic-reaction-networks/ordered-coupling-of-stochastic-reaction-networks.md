# Ordered coupling of stochastic reaction networks

**Setting.** Two continuous-time Markov chains $X$ and $Y$ on a common state space $E \subseteq \mathbb{Z}^d$ have rate matrices $q^X, q^Y$, extended by zero to jumps leaving $E$: $\bar q(x, x+\xi) = 0$ if $x + \xi \notin E$. A binary relation $\rho \subseteq E\times E$ encodes the desired order, for example $x \le y$ componentwise, or a linear order $Mx \le My$ on chosen species combinations.

**Theorem (pathwise comparison).** Suppose that for every $(x,y) \in \rho$ and every jump $\xi \in \mathbb{Z}^d$:
- (a) if $(x+\xi, y) \notin \rho$, then $\bar q^X(x,x+\xi) \le \bar q^Y(y,y+\xi)$;
- (b) if $(x, y+\xi) \notin \rho$, then $\bar q^X(x,x+\xi) \ge \bar q^Y(y,y+\xi)$;
- (c) if $(x+\xi, y+\xi) \notin \rho$, then $(x+\xi,y+\xi) \notin E\times E$.

Then for every $(x^0,y^0) \in \rho$ there are versions of $X$ and $Y$ on one probability space, with $X(0) = x^0$, $Y(0) = y^0$, such that

$$\mathbb{P}\bigl((X(t),Y(t)) \in \rho \ \text{ for all } t \in [0, \tau^X\wedge\tau^Y)\bigr) = 1,$$

where $\tau^X, \tau^Y$ are the explosion times.

**Reaction networks.** For a network with two monotone kinetics sharing the same functional forms and differing in rate constants $K^X$, $K^Y$, choosing $\rho$ through an integer matrix $M$ (together with the conservation laws $C$) turns (a)-(c) into finitely many linear sign conditions on the reaction vectors and on $K^X - K^Y$, which can be checked mechanically. Mass-action kinetics is a special case. This yields ordered couplings, and hence stochastic ordering of abundances, extinction times and moments, between a network under study and a simpler or better-understood comparison network.

## Depends on

- [Stability of randomly switching asymptotically linear reaction networks](stability-of-randomly-switching-asymptotically-linear-reaction-networks.md)

## Expansion

The coupling moves the two chains together along a common jump $\xi$ at rate $\min(\bar q^X, \bar q^Y)$ and lets each jump alone at the excess rate. A common jump never leaves $\rho$ by (c). A solo jump of $X$ that would break the order is impossible because (a) makes its excess rate zero, and symmetrically (b) rules out order-breaking solo jumps of $Y$. Since jumps of a reaction network are reaction vectors, the conditions need only be checked for finitely many $\xi$, and for linear relations they reduce to linear algebra on the stoichiometry and rate constants.

## Sources

- D. Cappelletti, G. Cuniberti, P. Siri, "Computable sufficient conditions for comparing stochastic reaction networks with mass-action or monotone kinetics" (2026), Theorem 3.1 and Theorem 4.1, <https://doi.org/10.48550/arXiv.2604.00756>.
