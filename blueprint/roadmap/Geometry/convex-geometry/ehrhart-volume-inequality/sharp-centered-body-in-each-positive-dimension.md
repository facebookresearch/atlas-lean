# Centered bodies attaining the Ehrhart constant

For every integer $n>0$ there exists a convex compact $K\subseteq\mathbb R^n$ with nonempty interior, zero barycenter and $\operatorname{int}(K)\cap\mathbb Z^n=\{0\}$ such that $V(K)=(n+1)^n/n!$.

## Depends on

- [Lattice-normalized volume and barycenter](lattice-normalized-volume-and-barycenter.md)
- [The centered dilation of the standard simplex](centered-simplex.md)

## Proof depends on

- [Barycenter of the centered simplex](barycenter-of-the-centered-simplex.md)
- [Lattice-normalized volume of the centered simplex](volume-of-the-centered-simplex.md)

## Proof outline

Use the centered simplex. Its strict coordinate inequalities force any interior integer coordinates to be nonnegative, and the strict sum inequality forces their sum to be zero. Check compactness, convexity and nonempty interior separately.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 8](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `exists_centeredBody_sharp`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/F_EhrhartVolumeInequality.lean#L56-L58)
