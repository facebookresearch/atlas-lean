# The kernel of an RKHS is a positive-definite kernel

Let $H$ be a real reproducing kernel Hilbert space of functions on $X$ with [feature
map](feature-map.md) $\varphi$. Then the kernel $k(x, y) = \langle \varphi(x), \varphi(y)\rangle$
is positive definite: every kernel matrix $(k(x_i, x_j))_{i,j}$ is symmetric positive
semidefinite. This is the converse direction of Aronszajn's theorem.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press, 2024, Section 7.3,
  Proposition 7.3.
