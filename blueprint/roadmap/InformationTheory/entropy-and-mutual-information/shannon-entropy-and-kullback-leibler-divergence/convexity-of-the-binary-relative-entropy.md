# Convexity of the binary relative entropy

Let $d$ be the binary relative entropy. For every $q \in [0, 1]$ the function $p \mapsto d(p, q)$, and for every
$p \in [0, 1]$ the function $q \mapsto d(p, q)$, is convex on $[0, 1]$ as a function with values in
$(-\infty, \infty]$: for $a, b, \lambda \in [0, 1]$,

$$
d\big(\lambda a + (1 - \lambda) b, q\big) \le \lambda\, d(a, q) + (1 - \lambda)\, d(b, q), \qquad
d\big(p, \lambda a + (1 - \lambda) b\big) \le \lambda\, d(p, a) + (1 - \lambda)\, d(p, b),
$$

in $(-\infty, \infty]$, with $0 \cdot \infty = 0$. Moreover $d(p, q) \ge 0$, with equality if and only if $p = q$. So $d(\cdot, q)$ has the
unique minimiser $q$ and $d(p, \cdot)$ the unique minimiser $p$.

## Proof

For $p, q \in (0, 1)$, $d(\cdot, q)$ is the negative binary entropy $h(p) = p \log p + (1 - p) \log (1 - p)$, whose
second derivative $\frac1p + \frac1{1 - p}$ is positive, plus an affine function of $p$; and $d(p, \cdot)$ is $h(p)$
plus the convex functions $p \log \frac1q$ and $(1 - p) \log \frac1{1 - q}$. The boundary values, where $d$ may be
infinite, are checked from the definition.

For the second claim, let $q \in (0, 1)$. Then $d(\cdot, q)$ is finite and continuous on $[0, 1]$, strictly convex,
and its derivative $\log \frac{p (1 - q)}{q (1 - p)}$ on $(0, 1)$ vanishes only at $p = q$, so $q$ is its unique
minimiser on $[0, 1]$; as $d(q, q) = 0$, $d(p, q) > 0$ for every $p \ne q$. For $q \in \{0, 1\}$, $d(p, q) = 0$ if
$p = q$ and $d(p, q) = \infty$ otherwise, by definition. So $d \ge 0$ and $d(p, q) = 0$ exactly when $p = q$, which
also gives the unique minimiser $p$ of $d(p, \cdot)$.

## Depends on

- [Binary relative entropy](binary-relative-entropy.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy,
  <https://tor-lattimore.com/downloads/book/book.pdf>), Lemma 10.2(a) and its proof.
