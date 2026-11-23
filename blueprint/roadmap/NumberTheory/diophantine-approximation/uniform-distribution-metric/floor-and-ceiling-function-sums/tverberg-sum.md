# Tverberg's sum

Let $F : \mathbb{R} \to \mathbb{Z}$, let $a = (a_1, \dots, a_\ell)$ be a
tuple of integers, let $m$ be a natural number and let $k$ be an integer. Tverberg's sum is
$f^{(F)}(a, m, k) = \sum_{T \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |T|}
F((k + \sum_{i \in T} a_i) / m)$, where the division is in $\mathbb{R}$ (with $x / 0 = 0$).

The paper takes $F = \lfloor \cdot \rfloor$ in Definition 1, and $F = \lceil \cdot \rceil$,
$x \mapsto \lfloor x + 1/2 \rfloor$ or $x \mapsto \lceil x - 1/2 \rceil$ in Section 1 and
Definition 3.

## Sources

- Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam, *Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3.
