# Integrability of the convolution integrand

Let $f, g : \mathbb{R}^d \to \mathbb{R}$ be Lebesgue integrable. Then the function
$(x, y) \mapsto f(x - y)\, g(y)$ is Lebesgue integrable on
$\mathbb{R}^{2d} = \mathbb{R}^d \times \mathbb{R}^d$.

## Idea

This is what makes the convolution of two integrable functions meaningful. By Tonelli's theorem and
the translation invariance of Lebesgue measure,
$\iint |f(x - y)\, g(y)|\, dx\, dy = \int |f| \cdot \int |g| < \infty$. Fubini's theorem then shows
that $(f * g)(x) = \int f(x - y)\, g(y)\, dy$ is defined for almost every $x$, that $f * g$ is
integrable, and that $\|f * g\|_1 \le \|f\|_1 \|g\|_1$.

## Statements

- [Integrability of the convolution integrand](integrable-comp-sub-mul-of-integrable-fi.md)
