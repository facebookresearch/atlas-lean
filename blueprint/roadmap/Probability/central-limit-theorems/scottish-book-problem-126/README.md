# Infinite-variance limit (Scottish Book Problem 126)

Let $f : \mathbb{R} \to \mathbb{R}$ be a measurable function that is integrable on $[0, 1]$ and
satisfies $\int_0^1 f(x)\,dx = 0$ and $\int_0^1 f(x)^2\,dx = \infty$. Then the complex numbers

$$\left(\int_0^1 \exp\left(i f(x) / \sqrt{n}\right) dx\right)^n$$

tend to $0$ as $n \to \infty$. Kac asked this as Problem 126 of the Scottish Book, and Khintchine
answered it affirmatively.

## Idea

With $U$ uniform on $[0, 1]$, the integral $\varphi(t) = \int_0^1 e^{i t f(x)} dx$ is the
characteristic function of the random variable $Y = f(U)$, which has mean $0$, and $\varphi(1/\sqrt{n})^n$
is the characteristic function at $1$ of $(Y_1 + \dots + Y_n)/\sqrt{n}$ for independent copies $Y_i$ of
$Y$. If the variance $A = \int_0^1 f^2$ were finite, the central limit theorem would give the limit
$e^{-A/2}$. With infinite variance the normalized sums spread out without bound, and the limit is $0$.
A direct argument: applying Fatou's lemma to $1 - |\varphi(t)|^2 = \mathbb{E}[1 - \cos(t(Y - Y'))]$,
with $Y'$ an independent copy of $Y$, shows $(1 - |\varphi(t)|^2)/t^2 \to \infty$ as $t \to 0$, and then
$|\varphi(1/\sqrt{n})|^{2n} \le \exp(-n(1 - |\varphi(1/\sqrt{n})|^2)) \to 0$.

## Statements

- [Kac's Scottish Book Problem 126](khintchine-infinite-variance-limit.md)

## Background

- [Lindeberg–Feller central limit theorem](../lindeberg-feller-central-limit-theorem/README.md): the
  finite-variance behaviour that this statement contrasts with.
