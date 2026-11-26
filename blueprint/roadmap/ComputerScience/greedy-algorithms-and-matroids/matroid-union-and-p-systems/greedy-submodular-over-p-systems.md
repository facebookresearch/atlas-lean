# Greedy submodular maximization over matroids and p-systems

Let $f : 2^E \to \mathbb{R}_{\ge 0}$ be monotone and submodular and $\mathcal{I}$ a $p$-system. The **greedy algorithm**, starting from $\emptyset$ and repeatedly adding a feasible element of maximum marginal gain until no feasible element remains, returns a maximal independent set $G$ with

$$
f(G) \ge \frac{1}{p + 1}\, f(O)
$$

for every $O \in \mathcal{I}$. For a single matroid this is the factor $1/2$, and it is tight for the greedy algorithm already for a matroid on three elements.

## Proof sketch

Charge the elements of $O$ to the greedy steps at which they ceased to be feasible; by the $p$-system property at most $p$ elements of $O$ are charged to each step, and submodularity bounds each charged marginal gain by the greedy gain of its step.

## Depends on

- [p-systems](p-systems.md)
- [Submodular set function](../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Proof depends on

- [Intersections of k matroids are k-systems](matroid-intersections-are-k-systems.md)

## Sources

- M. L. Fisher, G. L. Nemhauser and L. A. Wolsey, "An Analysis of Approximations for Maximizing Submodular Set Functions II", Mathematical Programming Study 8, 1978.
- G. Călinescu, C. Chekuri, M. Pál and J. Vondrák, "Maximizing a Monotone Submodular Function Subject to a Matroid Constraint", SIAM Journal on Computing 40(6), 2011.
