# Mex step for chocolate bars with two functions

Let $g, h : \mathbb{N} \to \mathbb{N}$
have the NS property, and let $x, y, z, c$ be natural numbers with $x \le g(z)$, $y \le h(z)$
and $c < x \oplus y \oplus z$, where $\oplus$ is nim-sum (bitwise exclusive or). Then
$c = u \oplus y \oplus z$ for some $u < x$, or $c = x \oplus v \oplus z$ for some $v < y$, or
$c = \min(g(w), x) \oplus \min(h(w), y) \oplus w$ for some $w < z$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Lemma 3 (b) (`integers-2025-G3-lem-3`).
