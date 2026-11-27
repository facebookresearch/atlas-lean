# The centered dilation of the standard simplex

Let $\Delta_n=\{x\in\mathbb R^n:x_i\ge0,\ \sum_i x_i\le1\}$. The centered simplex $K_n$ is the image under $x\mapsto(n+1)x-\mathbf 1$, where $\mathbf 1$ is the all-ones vector. Equivalently, its inequalities are $y_i\ge-1$ and $\sum_i y_i\le1$.

## Implementation notes

Prove the direct half-space description using the inverse affine map. Check the singleton interpretation in dimension zero and the full-dimensional convex-compact interpretation in positive dimensions.

## Sources

- [Pinned affine simplex definition](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/F_EhrhartVolumeInequality.lean#L15-L22)
