# Positive metric entropy on a full parameter tail

Use the [Standard map, vector growth, and metric entropy](standard-map-dynamics-and-entropy.md) with the natural-log finite-partition convention on the unit torus.

There exists $k_0>0$ such that $h_m(F_k)>0$ for every real $k\ge k_0$. The assertion is uniform on a tail, not a statement for a generic set of parameters.

## Depends on

- [Standard map, vector growth, and metric entropy](standard-map-dynamics-and-entropy.md)

## Proof depends on

- [Pesin’s entropy formula for area-preserving torus maps](pesin-formula-for-area-preserving-torus-maps.md)

## Expansion

Prove the two torus shears preserve normalized area and identify the normalized finite-word infimum with the canonical partition entropy. Extract the large-parameter positive-growth estimate independently of this entropy conclusion, then verify and apply the hypotheses of Pesin’s formula. The positive-growth estimate cannot be replaced by a parameter-generic statement.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StandardMapEntropy.lean#L10-L49) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/146.md).
- OpenAI, [Positive Metric Entropy for the Standard Map at Large Parameters](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf) (September 23, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
