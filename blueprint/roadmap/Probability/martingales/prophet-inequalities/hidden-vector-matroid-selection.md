# Hidden-vector matroid selection against worst order

For each full-ground matroid on $[n]$ there is a probability law on finite bit-string seeds and a rule chosen before the fixed nonnegative weights $w=(w_e)$. The seed designates a set of observed labels $J$. The online core sees the seed and the vector $s_e=w_e$ for $e\in J$, $s_e=0$ otherwise, along with the labelled weight prefix through the current arrival. The actual accepted set is the core's accepted prefix with $J$ removed; the observed labels cannot earn reward. For every seed, nonnegative weight vector, arrival permutation and prefix this actual set is independent.

Writing $R(w,r,\pi)$ for the sum of finally accepted weights, the guarantee is

$$
\mathbb E_r\big[\min_{\pi\in S_n} R(w,r,\pi)\big]\;\ge\;2^{-293}\max_{I\text{ independent}}\sum_{e\in I}w_e
$$

for each fixed $w\ge0$. The minimum is inside the seed expectation.

**Conventions.** Use the finite matroid and the measurable, irrevocable prefix decision rule with an observed-label mask as defined above.

## Depends on

- [Irrevocable matroid prefix rules](online-matroid-prefix-rule.md)

## Proof depends on

A seed-distributed matroid selection construction with a uniform guarantee against the worst suffix for each sampled observation set, and a bound comparing the resulting reward with the offline optimum.

## Expansion

Specify the sampling and the feasible core independently of the weight vector, then prove the weighted lower bound by decomposing the offline optimum into the strata used by the allocation rule. Keep the observed labels excluded and do not average the adversarial order as if it were uniform.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatroidSecretary.lean#L238-L240)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/111.md)
- [Accompanying manuscript: One Sample Suffices for Matroid Prophet Inequalities against an Almighty Adversary](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/final.pdf)
