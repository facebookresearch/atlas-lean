# Necessity in Blackwell's theorem: failure of the response condition gives a uniform distance gap

Let $I, J$ be finite with $I$ nonempty, $m : I \times J \to E$ a vector payoff into a real inner product space and $S \subseteq E$ nonempty, complete and convex. If the response condition fails for $(m, S)$, then there are a fixed mixed strategy $q \in \Delta(J)$ and $\delta > 0$ such that for every horizon $T \ge 1$ and every sequence $p_0, \ldots, p_{T-1} \in \Delta(I)$,

$$
\mathrm{dist}\Big(\frac1T \sum_{t<T} m(p_t, q),\ S\Big) \ge \delta .
$$

So a convex set is approachable if and only if the response condition holds.

## Proof sketch

Take $q$ without a response. The set $C = \{m(p,q) : p \in \Delta(I)\}$ is compact and convex and disjoint from $S$, so it has positive distance $\delta$ from $S$. Any average of points of $C$ lies in $C$ by convexity, hence stays at distance at least $\delta$.

## Depends on

- [Blackwell's characterization: response condition iff every containing halfspace is forceable](blackwell-response-halfspace-equivalence.md)

## Proof depends on

- [Blackwell's characterization: response condition iff every containing halfspace is forceable](blackwell-response-halfspace-equivalence.md)

## Sources

- David Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific Journal of Mathematics, 1956.
