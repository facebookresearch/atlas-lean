# Row relative entropy under deterministic message refinement

For any natural numbers $d,m$, let $P$ be the joint probability law of a
signal $S$ on the Euclidean unit sphere in $\mathbb R^d$, a message $W$ in a
countable measurable space with measurable singletons, and $m$ rows $X$ in
$\mathbb R^d$. Let the extra message values lie in another countable measurable
space with measurable singletons, and let $e$ be measurable on the joint
signal–message space. The actual rows need not have a Gaussian marginal or
be independent of $(S,W)$. Append $e(S,W)$ to $W$ to obtain the law $P'$. If
$(W,e(S,W))$ has finite Shannon entropy in nats, the extended nonnegative
relative entropy is unchanged. Each reference law is the corresponding
signal–message marginal times the law of $m$ independent standard Gaussian
rows in $\mathbb R^d$. The equality does not assert that this relative entropy
is finite.

## Sources

- [GaussianReplacement.lean, actualRowRefinement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L457-L466).
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
