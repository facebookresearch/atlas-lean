# IID nearest-neighbor environments and the annealed path law

At each site of $\mathbb Z^d$, an environment supplies one probability vector on the $2d$ signed coordinate steps. Take these vectors independently with common law. Given the environment, the path starts at the designated origin and the transition from position $x$ uses the probability vector attached to $x$. The environment is sampled once, not resampled on visits. The annealed path law averages this conditional Markov law over the product environment. Strict ellipticity asks for positivity of each step weight almost surely; uniform ellipticity asks for one deterministic strictly positive lower bound on all step weights. Escape in direction $\ell$ means $X_n\cdot\ell\to+\infty$.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectionalWalk.lean#L12-L92)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectionalBallisticity.lean#L10-L85)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VelocityHemisphere.lean#L10-L83)
