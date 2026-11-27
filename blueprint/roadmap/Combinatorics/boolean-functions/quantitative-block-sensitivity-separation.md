# Quantitative separation of block sensitivity and sensitivity

For each integer $d\ge1$ there is $n>0$ and a nonconstant total Boolean function $f:\{0,1\}^n\to\{0,1\}$ with $f(0^n)=0$ and

$$
\frac{\operatorname{bs}(f)}{s(f)^2}\ge\frac{2^d}{4(d+2)^2}.
$$

Sensitivity is the maximum over inputs of the number of single-coordinate flips that change the value. Block sensitivity is the maximum over inputs of the largest family of pairwise disjoint nonempty sets of coordinates such that flipping each set changes the value. The maxima are over the whole cube and the quotient is real.

## Depends on

- Coordinate/block flips and the two integer maxima on the finite cube.

## Proof outline

Separate construction and the two estimates, and show nonconstancy gives positive sensitivity via a cube path. Do not replace block sensitivity by the zero-input statistic or add the family documentation's stronger exponent claim.

- Boolean family construction with matching block lower and ordinary sensitivity upper estimates.

## Sources

- [Comparator statement: `OAI.Paper320.quantitative_separation`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SensitivitySeparation.lean#L30-L37)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/132.md)
