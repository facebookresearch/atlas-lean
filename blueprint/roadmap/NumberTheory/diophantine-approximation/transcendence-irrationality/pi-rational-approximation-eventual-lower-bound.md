# Eventual lower bounds for rational approximations to pi

For each real $\nu>2$ there exists an integer $Q\ge2$ such that for every pair of integers $p,q$
with $q\ge Q$,

$$
|\pi-p/q|\ge q^{-\nu}.
$$

Here $q$ is positive and the fraction need not be reduced. The cutoff may depend on $\nu$ but not
on the numerator.

## Expansion

Decompose the admissible interpolation matrix estimates and their nondegeneracy, then turn them into the eventual integer-denominator lower bound. Preserve the order of the exponent and cutoff quantifiers.

## Sources

- [PiExponent.lean — `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PiExponent.lean#L7-L16)
