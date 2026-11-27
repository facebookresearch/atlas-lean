# QMA-hardness of continuum electronic energy with unit nuclear charges

For every bit-string promise problem with a [verifier in the stated promise class](coulomb-promise-and-verifiers.md), there exists a many-one reduction with the stated deterministic polynomial-time stack-machine certificate to the stated continuum Coulomb energy promise with $Z_a=1$ for every nucleus. The output list stores only distinct rational positions (no charge fields), followed by a positive unary electron count and binary rational thresholds with gap at least one. Yes inputs satisfy $E\le a$ and no inputs $E\ge b$, with the same full normalized spinful antisymmetric form domain used to compute $E$ on both sides. No binding assumption, confinement potential, magnetic field or fixed orbital basis is included.

## Depends on

- [Encoding, form-domain and verifier conventions](coulomb-promise-and-verifiers.md)

## Expansion

Use the unit-charge construction to produce witnesses for both sides of the promise. Maintain integer electron count and rational nuclear positions through every scale change; bound the complete bit length including unary fields and separate the two energy estimates with gap at least one. Do not deduce the unit-charge restriction solely from hardness for arbitrary charges.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContinuumCoulombHardness.lean#L369-L547) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/275.md).
- OpenAI, [QMA-hardness of continuum Coulomb energy with unit nuclear charges](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/QMA-hardness-of-continuum-Coulomb-energy-with-unit-nuclear-charges-September-24-2026/QMA-hardness-of-continuum-Coulomb-energy-with-unit-nuclear-charges-September-24-2026.pdf) (September 24, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
