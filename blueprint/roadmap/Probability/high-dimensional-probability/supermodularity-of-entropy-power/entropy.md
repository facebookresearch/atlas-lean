# Differential entropy of a real random variable

Let $(\Omega, P)$ be a measure space and $X : \Omega \to \mathbb{R}$ a function. Let $g$ be the Radon–Nikodym derivative of the image measure of $P$ under $X$ with respect to Lebesgue measure, with values in $[0, \infty]$, and let $f = \tilde g$ be its real version, with $\tilde\infty = 0$. The differential entropy of $X$ is

$$H(X) = -\int_{\mathbb{R}} f(x) \log f(x)\, dx,$$

with $0 \log 0 = 0$, and $H(X) = 0$ when $f \log f$ is not Lebesgue integrable. The expression does not assume that $X$ has a density: for a point mass the derivative $g$ is zero almost everywhere and $H(X) = 0$. When $X$ is a random variable on a probability space whose law has a Lebesgue density with $f \log f$ integrable (see [finite-entropy densities](has-finite-entropy-density.md)), $H(X)$ is the usual differential entropy of that density.
