# f-statistics carry no sampling times

In a [drift model](drift-model.md) with [binary loadings](has-binary-loadings.md), let $S$ be a sample taken at an internal node $v$, with lineage $L_S$, and let $S'$ be a present-day population
whose lineage is $L_S \cup \{e'\}$ for a new pendant edge $e'$ below $v$, on the lineage of no other population, of drift length
$\ell_{e'} = 0$ (so its drift increment vanishes almost everywhere). Then $f_2(S, Y) = f_2(S', Y)$ for every population $Y$,
so every $f_3$ and $f_4$ involving $S$ equals the corresponding statistic with $S'$, since by [the symmetric-difference formula](f2-eq-sum-symm-diff.md) $e'$ contributes
$\ell_{e'} = 0$. The drift model has no time coordinate, so sampling times are not identified by f-statistics and must enter as
external constraints. With $\ell_{e'} = \ell > 0$ instead, $f_2(S', Y) = f_2(S, Y) + \ell$ for every $Y \ne S'$, and $f_2(S, S') = \ell$; the two models are then
not f-equivalent without changing other lengths. For instance, with two further populations $Y$ and $Z$, $f_2(S', Y) - f_2(S, Y) = f_2(S', Z) - f_2(S, Z) = f_2(S, S') = \ell$.

## Depends on

- [Admixture-graph drift model](drift-model.md)

## Proof depends on

- [f2 as a symmetric-difference drift length under binary loadings](f2-eq-sum-symm-diff.md)

## Sources

- N. Patterson et al., "Ancient admixture in human history", Genetics 192 (2012), 1065–1093, <https://doi.org/10.1534/genetics.112.145037>. The statement is derived above.
