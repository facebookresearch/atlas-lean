# The pigeonhole principle has degree-2 Positivstellensatz refutations

For $m \ge 2$ pigeons and $m - 1$ holes, the inequality translation of $\mathrm{PHP}^m_{m-1}$, with pigeon constraints $P_k = \sum_{\ell=1}^{m-1} x_{k\ell} - 1 \ge 0$ ($1 \le k \le m$) and hole constraints $H_{kk'\ell} = 1 - x_{k\ell} - x_{k'\ell} \ge 0$ ($k \ne k'$), together with the Boolean axioms, has a Positivstellensatz refutation of degree $2$, namely the identity

$$\sum_{k=1}^{m} P_k + \sum_{\ell=1}^{m-1} \Big(\sum_{k=1}^{m} x_{k\ell} - 1\Big)^2 + \sum_{\ell=1}^{m-1}\sum_{k=1}^{m}\sum_{k' \ne k} H_{kk'\ell}\, x_{k\ell} + (m-2)\sum_{\ell=1}^{m-1}\sum_{k=1}^{m}(x_{k\ell}^2 - x_{k\ell}) = -1,$$

in which every term is a nonnegative combination of constraints, products of a constraint with a variable, and squares.

## Proof sketch

Expand the identity: per hole, the square and the products with the hole constraints cancel all products $x_{k\ell}x_{k'\ell}$ with $k \ne k'$, the Boolean axioms with coefficient $m - 2$ cancel the squares $x_{k\ell}^2$, and the remaining linear terms cancel against $\sum_k P_k$, leaving $-m + (m - 1) = -1$. (Grigoriev, Hirsch and Pasechnik print the last coefficient as $m - 1$; expanding shows that $m - 2$ is the coefficient that makes the identity hold when the triple sum runs over ordered pairs $k \ne k'$.) (Derived, not stated by the source: for $n$ holes and any $m > n$ pigeons the same identity with the extra constant $m - n - 1$ is a degree-$2$ refutation of $\mathrm{PHP}^m_n$; for $n \ge 2$ there is no refutation of degree $1$, since the fractional point $x_{k\ell} = 1/n$ satisfies all linear constraints and evaluation at it is a degree-one pseudo-expectation; for $n = 1$, $P_1 + P_2 + H_{1,2,1} = -1$ is a degree-1 refutation.)

## Depends on

- [Inequality translation of CNF formulas for semialgebraic proofs](inequality-translation-of-cnf.md)
- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)

## Proof depends on

- [Degree-$d$ pseudo-expectations](pseudo-expectations.md)

## Sources

- D. Grigoriev, E. A. Hirsch and D. V. Pasechnik, "Complexity of Semialgebraic Proofs", Moscow Mathematical Journal 2(4), 647–679, 2002; ECCC report TR01-103: Example 2.1 (a static $\mathrm{LS}_+$ proof, of degree two, of the propositional pigeonhole principle with $m$ pigeons and $m - 1$ holes, inequalities (2.18)–(2.19)).
