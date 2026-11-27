# Ehrhart volume upper bound for centered convex bodies

Let $n>0$ and let $K$ be a convex compact subset of $\mathbb R^n$ with nonempty interior. If its barycenter is zero and $\operatorname{int}(K)\cap\mathbb Z^n=\{0\}$, then

$$V(K)\le \frac{(n+1)^n}{n!}.$$

Only interior lattice points are excluded; boundary lattice points are not. The statement is for general convex bodies with these properties, not just lattice polytopes.

## Depends on

- [Lattice-normalized volume and barycenter](lattice-normalized-volume-and-barycenter.md)

## Expansion

Separate the convex-geometric estimates in the cited proof from the measure normalization and lattice-point transfer. Prove the hypotheses for the general compact body rather than only for a simplex or for integral vertices.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 8](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `ehrhart_volume_inequality_for_sets`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/F_EhrhartVolumeInequality.lean#L65-L73)
