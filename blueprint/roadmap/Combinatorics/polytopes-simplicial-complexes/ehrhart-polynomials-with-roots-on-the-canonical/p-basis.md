# Symmetric basis polynomials

For natural numbers $d$ and $j$, let $b^d_j$ be the complex
polynomial $\prod_{i=0}^{d-1} (X + d - j - i)$. The polynomial $p^d_j$ is $b^d_j$ if $2j = d$, and
$b^d_j + b^d_{d-j}$ otherwise, where $d - j$ is truncated at $0$ (so $p^d_j = b^d_j + b^d_0$ when
$j > d$).

Statements that use $p^d_j$ assume $j \le d$, where the truncation plays no role.

## Sources

- Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*, INTEGERS 25 (2025), Article A68, definition of `pᵈⱼ`.
