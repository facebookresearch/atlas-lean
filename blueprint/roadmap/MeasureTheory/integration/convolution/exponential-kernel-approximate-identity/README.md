# Exponential kernel approximate identity

For every $f \in L^2(\mathbb{R})$,
$\lim_{n \to \infty} n \int_{\mathbb{R}} \int_{\mathbb{R}} f(x)\, f(y)\, e^{-2n|x - y|}\, dy\, dx = \int_{\mathbb{R}} f(x)^2\, dx$,
where $n$ runs through the natural numbers and the integrals are taken with respect to Lebesgue
measure.

## Idea

For $n \ge 1$ the kernels $k_n(t) = n e^{-2n|t|}$ are nonnegative, have integral $1$ and concentrate
at $0$ as $n$ grows: they form an approximate identity. The double integral times $n$ is
$\int f \cdot (k_n * f)$, and $k_n * f \to f$ in $L^2$ for such kernels, so by the Cauchy–Schwarz
inequality it tends to $\int f^2$.

## Statements

- [Exponential kernel approximate identity](tendsto-mul-integral-integral-exp-neg-tw.md)
