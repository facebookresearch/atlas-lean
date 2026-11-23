# Deviations of mean-zero sums on the cube

Let $f : \mathbb{R} \to \mathbb{R}$ be square-integrable on $[0,1]$ with $\int_0^1 f = 0$ and $\int_0^1 f^2 > 0$, and let $(a_n)$ be a sequence of positive reals with $a_n \to \infty$. Let $F_n$ be the set of points $(x_1, \dots, x_n) \in [0,1]^n$ with $|f(x_1) + \dots + f(x_n)| \ge a_n \sqrt{n}$. Then the Lebesgue measure of $F_n$ in $\mathbb{R}^n$ tends to $0$ as $n \to \infty$.

## Idea

Lebesgue measure on the cube $[0,1]^n$ is a probability measure under which the coordinates $x_1, \dots, x_n$ are independent and uniform on $[0,1]$. So $f(x_1), \dots, f(x_n)$ are independent, identically distributed, with mean $0$ and variance $\sigma^2 = \int_0^1 f^2$, and their sum has variance $n \sigma^2$: its typical size is $\sqrt{n}$. Chebyshev's inequality gives

$$m_n(F_n) \le \frac{n \sigma^2}{a_n^2 \, n} = \frac{\sigma^2}{a_n^2} \to 0 .$$

Deviations of larger order than $\sqrt{n}$ thus become rare. Taking $a_n = \varepsilon \sqrt{n}$ gives the weak law of large numbers in the language of measure theory, and the central limit theorem shows that $\sqrt{n}$ is the right scale: with $a_n$ constant, the measure of $F_n$ does not tend to zero.

## Statements

- [Large deviations of mean-zero sums on the cube have vanishing measure](tendsto-volume-abs-sum-ge-mul-sqrt.md)

## Background

- [Variance of the sample mean](../variance-of-the-sample-mean/README.md)
