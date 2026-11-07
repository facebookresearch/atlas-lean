# The (k, l)-Göbel sequence

For natural numbers $k$ and $l$, the $(k, l)$-Göbel sequence
is the sequence of rational numbers $g_{k,l}(n)$, $n \ge 0$, given by $g_{k,l}(0) = 0$,
$g_{k,l}(1) = l$ and, for $n \ge 1$,

$$g_{k,l}(n + 1) = \frac{g_{k,l}(n) \bigl(n + g_{k,l}(n)^{k-1}\bigr)}{n + 1},$$

where $k - 1$ is truncated subtraction, so the exponent is $0$ when $k = 0$.

The paper indexes from $n = 1$ and takes $k, l \ge 2$ (Lemma 5 also admits $k, l \ge 1$); the
value at $n = 0$ is a convention and plays no role.

## Sources

- Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024), Article 24.8.1, Definition 1.
