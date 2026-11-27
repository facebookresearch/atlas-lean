# Bochner's theorem

A function $f : \mathbb{R} \to \mathbb{C}$ is the characteristic function of a Borel probability measure $\mu$ on $\mathbb{R}$, that is, $f(t) = \int_{\mathbb{R}} e^{itx} \, d\mu(x)$ for every real $t$, if and only if $f$ is continuous, $f(0) = 1$, and $f$ is positive definite: for every $n \in \mathbb{N}$, all real $x_1, \dots, x_n$ and all complex $c_1, \dots, c_n$, the sum $\sum_{i=1}^{n} \sum_{j=1}^{n} \overline{c_i} \, c_j \, f(x_i - x_j)$ is a nonnegative real number.

## Idea

Bochner's theorem says exactly which functions are characteristic functions, so a candidate can be tested without first finding its measure. One direction is a computation: when $f$ is the characteristic function of $\mu$, the double sum equals $\int \bigl|\sum_j c_j e^{-i x_j x}\bigr|^2 \, d\mu(x) \ge 0$, while $f(0) = \mu(\mathbb{R}) = 1$ and continuity follows from dominated convergence. For the converse one builds probability measures whose characteristic functions converge pointwise to $f$; Lévy's continuity theorem, which needs $f$ continuous at $0$, then produces the measure. For example, $\cos t$ passes the test, and it is the characteristic function of the law giving mass $1/2$ to each of $-1$ and $1$. In machine learning the same theorem identifies the continuous positive definite shift-invariant kernels $k(x, y) = f(x - y)$ with Fourier transforms of finite measures.

## Statements

- [Bochner's theorem](bochner.md)
- [Characteristic functions](is-characteristic-fun.md): definition used in the main statement
- [Positive definite functions](is-positive-definite.md): definition used in the main statement
- [Real-valued characteristic functions](is-characteristic-fun-real.md): definition, real-valued variant
- [Positive definite real-valued functions](is-positive-definite-real.md): definition, real-valued variant
- [Forward direction of Bochner's theorem](bochner-forward.md): forward direction
- [Real-valued characteristic functions are continuous and positive definite](bochner-forward-real.md): forward direction, real-valued case
- [Characteristic functions are positive definite](char-fun-is-positive-definite.md): forward direction, positive definiteness only

## Related topics

- [Random Fourier features](../../../ComputerScience/machine-learning/supervised-learning/random-fourier-features/README.md): sampling frequencies from the measure that Bochner's theorem attaches to a shift-invariant kernel gives an unbiased random approximation of the kernel.

## Sources

- S. Bochner, *Monotone Funktionen, Stieltjessche Integrale und harmonische Analyse*, Mathematische Annalen (1933).
