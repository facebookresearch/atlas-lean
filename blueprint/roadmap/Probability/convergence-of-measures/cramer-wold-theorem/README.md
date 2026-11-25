# Cramér–Wold device

Let $d \in \mathbb{N}$, let $(\Omega, \mu)$ and $(\Omega', \mu')$ be probability spaces, and let $X_n : \Omega \to \mathbb{R}^d$ ($n \in \mathbb{N}$) and $Z : \Omega' \to \mathbb{R}^d$, with $\mathbb{R}^d$ carrying the Euclidean inner product. If for every $t \in \mathbb{R}^d$ the real random variables $\langle t, X_n \rangle$ converge in distribution to $\langle t, Z \rangle$, then $X_n$ converges in distribution to $Z$. Here convergence in distribution means that each $X_n$ and the limit are almost everywhere measurable and their laws converge weakly as probability measures.

## Idea

The device reduces convergence of random vectors to convergence of real random variables, one direction at a time. Convergence of each coordinate is not enough: with $U$ standard normal, every coordinate of $X_n = (U, (-1)^n U)$ has the same normal law for all $n$, but the joint law alternates between two different laws, so $X_n$ does not converge in distribution. Projections in all directions do suffice. The proof uses characteristic functions: $\mathbb{E}\, e^{i \langle t, X_n \rangle}$ is the characteristic function of $\langle t, X_n \rangle$ at $1$, so the hypothesis gives pointwise convergence of the characteristic functions of $X_n$, and Lévy's continuity theorem concludes. A standard application derives the multivariate central limit theorem from the one-dimensional one.

## Statements

- [Cramér–Wold device](cramer-wold-device.md)

## Background

- [Lévy's continuity theorem](../../characteristic-functions/levy-continuity-theorem/README.md)

## Sources

- H. Cramér and H. Wold, *Some theorems on distribution functions*, Journal of the London Mathematical Society (1936).
