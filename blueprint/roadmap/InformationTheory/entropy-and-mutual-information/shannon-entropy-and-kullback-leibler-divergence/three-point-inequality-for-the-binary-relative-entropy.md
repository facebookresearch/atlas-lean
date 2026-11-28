# Three-point inequality for the binary relative entropy

Let $d$ be the binary relative entropy and let $p, q, \varepsilon \in [0, 1]$ with $p \le q - \varepsilon$. Then, in
$(-\infty, \infty]$,

$$
d(p, q - \varepsilon) + d(q - \varepsilon, q) \le d(p, q),
$$

and consequently $d(p, q - \varepsilon) + 2\varepsilon^2 \le d(p, q)$.

When $d(p, q) < \infty$, all the values involved are real numbers and these read
$d(p, q - \varepsilon) \le d(p, q) - d(q - \varepsilon, q) \le d(p, q) - 2\varepsilon^2$; written with sums they also cover
$d(p, q) = \infty$. With $r = q - \varepsilon$: for $0 \le p \le r \le q \le 1$,
moving the second argument of $d(p, \cdot)$ from $q$ down to $r$ lowers it by at least $d(r, q) \ge 2 (q - r)^2$.

## Proof

If $0 < q - \varepsilon$ and $q < 1$, then $d(x, q - \varepsilon)$ and $d(x, q)$ are real numbers for every
$x \in [0, 1]$, and the real function

$$
x \mapsto d(x, q - \varepsilon) - d(x, q) = x \log \frac{q}{q - \varepsilon} + (1 - x) \log \frac{1 - q}{1 - q + \varepsilon}
$$

is affine and nondecreasing on $[0, 1]$, so its value at $p$ is at most its value at $q - \varepsilon$, which is
$-d(q - \varepsilon, q)$. If $q - \varepsilon = 0$, then $p = 0$ and both sides equal $d(0, q)$. If $q = 1$ and
$\varepsilon > 0$, then $d(p, 1) = \infty$; if $\varepsilon = 0$ there is nothing to prove. The second inequality
follows from $d(q - \varepsilon, q) \ge 2\varepsilon^2$, the binary Pinsker inequality when $0 < q < 1$, and
immediate from the definition otherwise.

## Depends on

- [Binary relative entropy](binary-relative-entropy.md)

## Proof depends on

- [Binary Pinsker inequality on the closed interval](../../information-inequalities/binary-pinsker-of-mem-icc.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy,
  <https://tor-lattimore.com/downloads/book/book.pdf>), Lemma 10.2(c) and its proof, which uses Lemma 10.2(b),
  $d(p, q) \ge 2 (p - q)^2$.
