# Salem–Zygmund central limit theorem for lacunary sine sums

Let $(r_k)_{k \ge 0}$ be a sequence of positive integers with Hadamard gaps: there is $q > 1$ such that
$r_{k+1} / r_k \ge q$ for every $k$. Then for all real numbers $a < b$, the Lebesgue measure of the set
of $x \in [0, 1]$ with

$$a < \frac{1}{\sqrt{n}} \sum_{k=0}^{n-1} \sin(2 \pi r_k x) < b$$

tends to $\frac{1}{\sqrt{\pi}} \int_a^b e^{-y^2} \, dy$, the mass of $(a, b)$ under the normal law with
mean $0$ and variance $1/2$, as $n \to \infty$. In particular this holds for $r_k = 2^k$ and for
$r_k = 2^{k^2}$.

## Idea

For $x$ uniform in $[0, 1]$, each function $\sin(2\pi r_k x)$ has mean $0$ and mean square $1/2$, and
two of them with distinct positive frequencies are orthogonal. They are not independent, but when the
frequencies grow geometrically they behave almost like independent random variables: a product of a few of
them has mean zero unless a signed sum $\pm r_{k_1} \pm \dots \pm r_{k_j}$ of their frequencies vanishes,
and geometric growth makes such cancellations rare, so their normalized sums are asymptotically Gaussian with variance
$1/2$. Lacunary series are a model case of dependent sequences that still obey the classical limit laws
of probability. Kac's Problem 161 of the Scottish Book asks whether the same conclusion holds for
sequences of positive integers with $r_n - (r_0 + \dots + r_{n-1}) \to +\infty$. This condition
differs from the Hadamard-gap condition above: $r_n = 2^n$ has Hadamard gaps with $q = 2$ but does not
satisfy it. For arbitrary integer sequences the answer is no: the constant sequence $r_k = -1$
satisfies the condition, but its normalized sum $-\sqrt{n} \sin(2 \pi x)$ is not asymptotically normal.

## Statements

- [Salem–Zygmund central limit theorem for lacunary sine sums](kac-lacunary-central-limit-theorem.md)
- [Central limit theorem for lacunary sine sums](lacunary-clt.md): definition used in the main statement

## Sources

- R. Salem and A. Zygmund, "On lacunary trigonometric series", Proceedings of the National Academy of
  Sciences of the United States of America (1947).
