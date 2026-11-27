# Regular variation of the count of distinct totients

For each fixed real $c>0$,

$$
\lim_{x\to+\infty}\frac{V(cx)}{V(x)}=c,
$$

where $x$ is real and $V(x)$ counts distinct positive totient values at most $x$.

## Depends on

- [Distinct totient count and normalization](totient-counting-normalization.md)

## Proof depends on

- [Totient asymptotic equivalent](totient-count-asymptotic.md)

## Expansion

Analyze dilation of $U(x)$ and the phase-dependent multiplier jointly, controlling the possible crossing of an integer boundary of the phase. Boundedness and positivity of the phase factor alone do not imply regular variation.

## Sources

- [TotientAsymptotic.lean — `totient_asymptotic_formula`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L118-L127)
