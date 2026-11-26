# Lattice-normalized volume and barycenter

In $\mathbb R^n$ with lattice $\mathbb Z^n$, take Lebesgue measure with unit cube of volume one. For a convex compact body $K$ with nonempty interior, its normalized volume $V(K)$ is this Lebesgue measure as a real number, without an extra factor of $n!$. Its barycenter is $V(K)^{-1}\int_K x\,dx$, integrating the vector coordinatewise. The interior lattice points are $\{z\in\mathbb Z^n:z\in\operatorname{int} K\}$. A centered body in this setting has barycenter zero and exactly the origin as an interior lattice point.

## Implementation notes

Use Euclidean Lebesgue measure in coordinate space with the lattice covolume convention; prove positive finite volume and integrability on the specified bodies before converting the measure to a real.

## Sources

- [Pinned measure, barycenter and body conventions](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/F_EhrhartVolumeInequality.lean#L10-L42)
