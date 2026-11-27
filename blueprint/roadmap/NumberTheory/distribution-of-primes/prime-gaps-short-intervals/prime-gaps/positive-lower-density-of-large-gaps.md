# Positive lower density of large consecutive prime gaps

Write $p_n$ for the $n$th prime with $p_1=2$. For every real $C>0$ there are a real $c>0$ and a
natural $N_0$ such that for every natural $N\ge N_0$,

$$
 cN\le \#\{1\le n\le N:p_{n+1}-p_n>C\log p_n\}.
$$

The constants may depend on $C$. The bound holds for all sufficiently long initial segments, not
merely infinitely many. The comparison with $C\log p_n$ is strict.

## Depends on

- [Prime gaps](prime-gap.md)

## Proof depends on

- [Bombieri–Vinogradov theorem](../../primes-in-progressions/bombieri-vinogradov-theorem/bombieri-vinogradov.md), for the average residue-class error used in the gap detector.

## Expansion

Specialize the maximum-over-endpoints average to a single endpoint, and pass from the integer
endpoint to the real cutoff by flooring and allowing a larger logarithmic loss in the modulus
cutoff. Then isolate the covering and sieve estimates for a positive proportion of gaps,
including the reindexing to the first $N$ primes. An unbounded normalized gap limsup does not
supply a positive lower density.

## Sources

- [PrimeGaps.lean — `large_gaps_and_ratio_density`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PrimeGaps.lean#L36-L42)
- [Endpoint error and Bombieri–Vinogradov input](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/PrimeGaps/MangoldtBounds.lean#L87-L105)
- [Large-gap density from the average error estimate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/PrimeGaps/Main.lean#L158-L164)
