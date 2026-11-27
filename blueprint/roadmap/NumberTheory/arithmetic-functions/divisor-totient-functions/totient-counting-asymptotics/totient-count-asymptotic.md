# An asymptotic equivalent for the number of distinct totients

For real $x\to+\infty$, the number of distinct totient values satisfies

$$
\frac{V(x)}{U(x)A(1;\theta(x))}\longrightarrow1.
$$

Here $U$ is the renewal normalization and $A(1;\theta(x))$ the unweighted arithmetic coefficient
at the varying phase, not a constant presumed independent of phase.

## Depends on

- [Renewal normalization and phase](totient-counting-normalization.md)
- [Arithmetic coefficient](finite-coefficients.md)

## Proof depends on

- [Uniform positive coefficient limit](unweighted-coefficient-positive-bounds.md)

## Expansion

Prove the normalized count estimate by a fixed-band approximation with uniform discard bounds on exceptional tuples and then let the band grow. Use the positive lower bound on $A(1;s)$ to replace additive normalized errors by an asymptotic ratio.

## Sources

- [TotientAsymptotic.lean — `totient_asymptotic_formula`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L118-L127)
