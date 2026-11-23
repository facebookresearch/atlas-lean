# Blackwell's condition for regret-invariant play

If the mixed action $q$ is regret-invariant for $\lambda$, then for every vector $g$ of payoffs

$$\sum_{j, k} \lambda(j, k)\, q(j)\,\bigl(g(k) - g(j)\bigr) = 0 .$$

Taking for $\lambda$ the current regrets and $g = u_i(\cdot, s_{-i})$ for an arbitrary
opponents' profile, this is Blackwell's condition (3.3) for approaching the nonpositive orthant of
regret vectors, with equality. It is the algebraic core of the proof of Theorem A of Hart and
Mas-Colell: regret-invariant play drives the positive parts of the average conditional regrets to zero (the
average regret vector approaches the nonpositive orthant), and then the empirical distribution to the
set of correlated equilibria.

## Background

- [Regret-invariant mixed action](is-regret-invariant.md): the hypothesis, used to telescope the
  double sum.
- [Blackwell approachability](../blackwell-approachability/README.md): the theorem this condition
  feeds.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, proof of Theorem A, (3.3).
