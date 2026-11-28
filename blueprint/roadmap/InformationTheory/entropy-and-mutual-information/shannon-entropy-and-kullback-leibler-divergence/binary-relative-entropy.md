# Binary relative entropy

For $p, q \in [0, 1]$, the binary relative entropy $d(p, q) \in (-\infty, \infty]$ is

$$
d(p, q) = p \log \frac{p}{q} + (1 - p) \log \frac{1 - p}{1 - q},
$$

with the natural logarithm and the conventions $0 \log \frac{0}{a} = 0$ for $a \ge 0$ and $a \log \frac{a}{0} = \infty$
for $a > 0$. Each term then lies in $(-\infty, \infty]$, where the sum is defined, and is a real number when
$p, q \in (0, 1)$. On the boundary of the square this gives $d(0, q) = \log \frac{1}{1 - q}$ and $d(1, q) = \log \frac{1}{q}$
for $q \in [0, 1]$; $d(p, 0) = 0$ if $p = 0$ and $d(p, 0) = \infty$ otherwise; $d(p, 1) = 0$ if $p = 1$ and
$d(p, 1) = \infty$ otherwise. In particular $d(0, 1) = d(1, 0) = \infty$. These are the values of the source, which
obtains them as limits of the formula along the edges of the square.

The value $d(p, q)$ is the
[relative entropy between the Bernoulli laws](relative-entropy-between-bernoulli-laws.md) of parameters $p$ and
$q$, hence its name; in particular it is nonnegative, as the
[convexity page](convexity-of-the-binary-relative-entropy.md) also shows directly.

## Background

- [Binary Pinsker inequality on the closed interval](../../information-inequalities/binary-pinsker-of-mem-icc.md):
  the bound $d(u, v) \ge 2 (u - v)^2$ for $u \in [0, 1]$ and $v \in (0, 1)$, written with the formula above.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy,
  <https://tor-lattimore.com/downloads/book/book.pdf>), Definition 10.1.
- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025
  (prepublication version of 16 August 2024, with the published numbering), Example 2.1, eq. (2.6) (binary
  divergence).
