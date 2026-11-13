# The sets $\mathrm{CST}_k$

Fix $r, k \in \mathbb{N}$. For a digit sequence
$x = (x_i)_{i \in \mathbb{N}}$ in $\{0, 1\}$ let $v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, where $F_i$
is the $i$-th Fibonacci number ($F_1 = F_2 = 1$). The set $\mathrm{CST}_k$ (for the shift $r$)
consists of the digit sequences $x$ such that either $v_k(x) + r < F_{k+1}$, or both
$F_{k+1} \le v_k(x)$ and $v_k(x) + r < F_{k+2}$.

In terms of the Rokhlin towers of order $k$, this is the union of the levels of the large and the
small tower except the $r$ highest levels of each tower.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Section 5.1 (definition of `CST_k`).
