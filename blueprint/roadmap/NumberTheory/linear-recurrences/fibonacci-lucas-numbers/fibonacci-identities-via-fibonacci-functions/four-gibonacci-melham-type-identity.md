# Four-sequence Melham-type identity for gibonacci sequences

Let
$G, H, I, J : \mathbb{Z} \to \mathbb{R}$ satisfy $G_{j+2} = G_{j+1} + G_j$ for every integer $j$,
and likewise $H$, $I$ and $J$, and let $F_m$ denote the Fibonacci numbers. For every natural
number $n$ and all integers $k$, $r$, $s$ and $t$, writing
$S(X, x; Y, y) = \sum_{j=0}^{2n-1} X_{x+j} Y_{y+j}$ for sequences $X, Y$ and integers $x, y$,

$$
2 S(G, k; J, t) S(H, r; I, s) + 2 S(I, s; J, t) S(G, k; H, r) +
2 S(G, k; I, s) S(H, r; J, t)
= F_{2n}^2 \big(G_{k+n-2} H_{r+n-2} I_{s+n-2} J_{t+n-2} +
4 G_{k+n-1} H_{r+n-1} I_{s+n-1} J_{t+n-1} + 4 G_{k+n} H_{r+n} I_{s+n} J_{t+n} +
G_{k+n+1} H_{r+n+1} I_{s+n+1} J_{t+n+1}\big).
$$

The source leaves $n$ unquantified; it is taken to be a natural number.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 34 (`jis-2024-24.6.2-prop-34`).
