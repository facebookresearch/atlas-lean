# Conditional information from marginal kernels

For a finite measure $Q$ of $(Z,A,B)$ on a measurable conditioning space and two standard Borel spaces, disintegrate on $Z$ to obtain a kernel $K(z,d(a,b))$ on the row–message pair. Write $K_A,K_B$ for its coordinate marginals. Let $R$ be the composition-product of $Q_Z$ with $K_A(z)\otimes K_B(z)$. The conditional mutual information in nats is the extended nonnegative $D(Q\Vert R)$. If the pair space is empty, use zero. For a probability $Q$, changing any of these kernels on a $Q_Z$-null set does not change its composition-product. This is not the finite-PMF definition, and no ordinary real subtraction of possibly infinite entropies occurs.

For exposed information in an actual row law of $(S,W,G)$, apply this definition with $Z=(G,GS)$, $A=S$ and $B=W$. Fresh exposed information at width $k$ is obtained by adjoining $k$ independent Gaussian rows to the given signal-state law before applying the same operation; the block average takes the totalized real projections over the inclusive prescribed range of widths. The actual law itself need not be that product law.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L96-L103)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L220-L255)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L268-L316)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PosteriorReplicas.lean#L74-L77)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PosteriorReplicas.lean#L258-L262)
