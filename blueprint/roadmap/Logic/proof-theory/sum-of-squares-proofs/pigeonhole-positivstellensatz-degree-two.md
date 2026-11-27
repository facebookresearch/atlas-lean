# The pigeonhole principle has degree-2 Positivstellensatz refutations but none of degree 1

For $m > n$, the inequality translation of $\mathrm{PHP}^m_n$ with the Boolean axioms has a Positivstellensatz refutation of degree $2$, namely the identity

$$\sum_i P_i + \sum_j \Big(1 - \sum_i x_{ij}\Big)^2 + \sum_j \sum_{i \ne i'} x_{ij} H_{ii'j} + (m - n - 1) + (m-2)\sum_{i,j}(x_{ij}^2 - x_{ij}) = -1$$

with pigeon constraints $P_i = \sum_j x_{ij} - 1 \ge 0$ and hole constraints $H_{ii'j} = 1 - x_{ij} - x_{i'j} \ge 0$; for $n \ge 2$ it has no refutation of degree $1$, since the fractional point $x_{ij} = 1/n$ satisfies all linear constraints (for $n = 1$, $P_1 + P_2 + H_{1,2,1} = -1$ is a degree-1 refutation).

## Proof sketch

Expand the identity; for degree one, evaluation at the uniform fractional point is a degree-one pseudo-expectation.

## Depends on

- [Inequality translation of CNF formulas for semialgebraic proofs](inequality-translation-of-cnf.md)
- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)

## Proof depends on

- [Degree-$d$ pseudo-expectations](pseudo-expectations.md)

## Sources

- D. Grigoriev, E. A. Hirsch and D. V. Pasechnik, "Complexity of Semialgebraic Proofs", Moscow Mathematical Journal 2(4), 647–679, 2002.
