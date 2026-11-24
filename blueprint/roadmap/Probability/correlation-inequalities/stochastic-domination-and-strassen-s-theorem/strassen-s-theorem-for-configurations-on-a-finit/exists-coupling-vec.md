# Strassen's theorem for nonnegative vectors on a finite poset

Let $P$ be a finite partially ordered set and $\mu, \nu : P \to \mathbb{R}$ nonnegative with equal total mass, $\sum_x \mu(x) = \sum_x \nu(x)$. If

$$\sum_{x \in D} \nu(x) \le \sum_{x \in D} \mu(x) \quad \text{for every down-set } D \subseteq P,$$

then there is a nonnegative function $c$ on the [ordered pairs](order-pairs.md) $\{(x, y) : x \le y\}$ with first marginal $\mu$ and second marginal $\nu$:

$$\sum_{y \ge x} c(x, y) = \mu(x), \qquad \sum_{x \le y} c(x, y) = \nu(y) \qquad \text{for all } x, y \in P.$$

This is the ordered-pair form of [Strassen's theorem on a finite poset](../finite-strassen-stochastic-domination/forall-is-upper-set-sum-le-iff-exists-co.md) (comparison on down-sets is equivalent to the reverse comparison on their complements, the upper sets).

## Sources

- V. Strassen, *The existence of probability measures with given marginals*, Ann. Math. Statist. 36 (1965), 423–439.
