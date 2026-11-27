# Kernel of the dual map has the same dimension as the kernel

Let $V$ be a finite-dimensional vector space over a field $K$ and $f : V \to V$ a linear map. Then the
kernel of the dual map $f^* : V^* \to V^*$ has the same dimension as the kernel of $f$.

## Idea

The dual map sends a linear form $\ell$ to $\ell \circ f$, so $\ell$ lies in its kernel exactly when
it vanishes on the range of $f$: the kernel of $f^*$ is the annihilator of the range. In finite
dimension the annihilator of a subspace has dimension $\dim V$ minus the dimension of the subspace,
and by rank–nullity so does $\ker f$. In matrix terms, a square matrix and its transpose have the same
rank.

## Statements

- [Kernel of the dual map has the same dimension as the kernel](finrank-ker-dual-map-eq-finrank-ker.md)
