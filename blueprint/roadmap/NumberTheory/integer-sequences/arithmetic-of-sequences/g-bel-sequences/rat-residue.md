# Residue of a rational number modulo an integer

For a natural number $m$ and a rational
number $x = a/b$ in lowest terms with $b > 0$, the residue of $x$ modulo $m$ is the element
$a \cdot b^{-1}$ of $\mathbb{Z}/m\mathbb{Z}$. When $b$ is prime to $m$, $b^{-1}$ is the inverse
of $b$ modulo $m$, so the residue is the class $c$ with $b c \equiv a \pmod m$. In general, for
$m \ge 1$, $b^{-1}$ denotes the class of the Bézout coefficient $u$ given by the extended Euclidean
algorithm, $u b + v m = \gcd(b, m)$; for $m = 0$, where $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$,
$b^{-1} = 1$ and the residue is $a$.

For a prime $p$ and a natural number $r$, it is used to read congruences modulo $p^r$ in the
ring $\mathbb{Z}_{(p)}$ of rational numbers whose denominator is prime to $p$.

## Sources

- Hibiki Gima, Toshiki Matsusaka, Taichi Miyazaki, and Shunta Yara, *On Integrality and Asymptotic Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024), Article 24.8.1, Section 4 (residues of $g_{k,l}(n)$ modulo $p^r$ in $\mathbb{Z}_{(p)}$).
