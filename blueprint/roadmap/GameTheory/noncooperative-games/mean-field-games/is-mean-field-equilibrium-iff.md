# Equilibria are supported on minimisers

A probability vector $m$ is a [mean field equilibrium](is-mean-field-equilibrium.md) if and only if
every state charged by $m$ minimises the cost: $m(x) \ne 0$ implies $F(x, m) \le F(y, m)$ for every
$y$.

If some charged $x$ had $F(y, m) < F(x, m)$, moving the mass $m(x)$ from $x$ to $y$ would lower
$\sum_y F(y, m) m'(y)$ by $m(x)(F(x, m) - F(y, m)) > 0$. Conversely, if $m$ is supported on minimisers
then $\sum_y F(y, m) m(y) = \min F(\cdot, m) \le \sum_y F(y, m) m'(y)$. Cardaliaguet tests with Dirac
masses $m' = \delta_x$ instead; on a finite set both arguments work.

## Sources

- P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*, version of 27 September 2013, Remark 2.5.
