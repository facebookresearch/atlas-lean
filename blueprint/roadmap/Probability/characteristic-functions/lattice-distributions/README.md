# Lattice distributions

A measure $\mu$ on $\mathbb{R}$ with characteristic function $\varphi(t) = \int e^{itx} \, d\mu(x)$ is a lattice distribution (a lattice random variable) if $\varphi(l) = 1$ for some real $l \ne 0$ and $\varphi(t) \ne 1$ for some real $t$. For a probability measure the second condition says that $\mu$ is not the point mass at $0$.

## Idea

For a probability measure $\mu$ and a real $l \ne 0$, $\varphi(l) = 1$ holds exactly when $\mu$ gives mass $1$ to the lattice $\{(2\pi / l) k : k \in \mathbb{Z}\}$: the real part $\int \cos(lx) \, d\mu(x)$ can only equal $1$ if $\cos(lx) = 1$ for $\mu$-almost every $x$. So a lattice distribution is a law carried by the multiples of a nonzero step $h$, and its characteristic function is then periodic with period $2\pi / h$. Binomial laws with $n \ge 1$ trials and success probability $p > 0$, and Poisson laws with positive mean are examples, with $h = 1$ and $\varphi(2\pi) = 1$. The distinction matters in local limit theorems, where lattice laws need a separate treatment. Many textbooks use a broader notion, a law carried by a shifted lattice $a + h\mathbb{Z}$, detected by $|\varphi(l)| = 1$; the condition here fixes the lattice through $0$.

## Statements

- [Lattice random variable](is-lattice-rv.md)
- [Lattice random variables are supported on a lattice](exists-lattice-support.md): basic property: support on a lattice
- [A characteristic function equal to one detects lattice support](char-fun-eq-one-iff-measure-eq-one-of-la.md): characteristic-function criterion, used for the support property
