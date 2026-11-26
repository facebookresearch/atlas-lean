# Matroid secretary selection with a uniform observation prefix

For every matroid on all $n$ labels, there exist a finite seed law and a measurable rule chosen independently of the nonnegative fixed weights. The seed sets an observation length $K\in\{0,\ldots,n\}$. The rule rejects the first $K$ arrivals and thereafter uses only the seed and the labelled weight prefix including the current arrival. For every seed, nonnegative weight vector, permutation and time, the accepted set is independent.

On any probability space, let the seed and a uniform reference permutation $\sigma$ of all $n$ labels be independent and measurable with the prescribed laws. Any measurable actual permutation $\pi$ is allowed provided that its first $K$ labels agree in order with $\sigma$ almost surely. The actual reward is integrable, and its expectation is at least $2^{-293}$ times the offline maximum independent-set weight. No independence assumption is imposed on the suffix of $\pi$.

**Conventions.** Use a uniform permutation, an independent finite seed, and a measurable observation-length and online decision map with the prefix constraints above.

## Depends on

- [Irrevocable matroid prefix rules](online-matroid-prefix-rule.md)

## Proof depends on

- [Hidden-vector matroid selection against worst order](hidden-vector-matroid-selection.md)

## Expansion

Verify the sampling bridge from the observed set and extra seed randomness to a uniform ordered prefix of seed-chosen length. Check both extreme prefix lengths and retain the adversarial conditioning on the suffix.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatroidSecretary.lean#L241-L243)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/111.md)
- [Accompanying manuscript: One Sample Suffices for Matroid Prophet Inequalities against an Almighty Adversary](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/final.pdf)
