# Shifting the interval can greatly increase the least length

For natural numbers $n$ and
$m$, let $f(n, m)$ be the least natural number $L$ such that the interval $(m, m + L]$ contains
distinct multiples of $1, \dots, n$. For all sufficiently large natural numbers $n$ there is a
positive integer $m$ with

$$
f(n, m) - f(n, n) > \frac{0.36\, n \log n}{\log \log n}.
$$

Since $f(n, m)$ is periodic in $m$ with period $\operatorname{lcm}(1, \dots, n)$, this says that
$\max_{m \ge 1} f(n, m) - f(n, n) > 0.36\, n \log n / \log \log n$ for all large $n$, the form
stated in the source.

## Sources

- Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the First n Positive Integers*, INTEGERS 26 (2026), Article A7, Theorem 1.
