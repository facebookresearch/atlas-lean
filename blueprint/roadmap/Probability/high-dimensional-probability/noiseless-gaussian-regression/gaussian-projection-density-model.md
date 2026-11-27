# Noiseless Gaussian row and label density models

For the unit sphere of the Euclidean space $\mathbb R^d$, labels of a vector $s$ under rows $A$ are $As=(\langle A_i,s\rangle)_i$. An independent row law $\gamma_m$ is the product of $m$ standard Gaussian vector laws. An actual law of $(S,W,X)$ may couple $X$ to the message even when the $(S,X)$ marginal is a product. Appending independent rows is a product on the entire actual law; projecting to $(A,W,AS)$ defines the joint observation law, not a fresh conditional experiment unless that assertion is proved.

The reference measure for a joint row/label density is standard Gaussian row law times Lebesgue label volume. Exact per-row label distributions are pushforwards by the corresponding linear label map. Smoothed densities use the specific averaging kernel in the stated result (cubes, Euclidean balls, or Gaussian convolution); their totalized density limits must not be identified on singular comparison laws merely by equality almost everywhere in the label.

For rectangular smoothing with label dimension $k$ and $\delta>0$, define $D_\delta(\rho;G,y)$ as $(2\delta)^{-k}$ times the mass of the closed coordinate cube of radius $\delta$ about $y$ under the label map. The exact candidate $D_0$ takes the real limit of the real projections along $\delta=1/j$ if it exists, embeds it into the extended nonnegative reals, and otherwise uses zero. The ball-average lower density instead uses the extended lower limit of closed-ball mass divided by ball volume. Gaussian regularization integrates the product label Gaussian densities in the signal measure, and its pointwise version takes the real limit along $1/j$ with zero if absent. These are distinct conventions and need not give the same value at every fixed label.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L12-L96)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MemoryPrecision.lean#L142-L311)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PosteriorReplicas.lean#L14-L33)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ProjectionMoments.lean#L324-L346)
