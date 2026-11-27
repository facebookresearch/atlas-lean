# Two-sequence Catalan-type identity for gibonacci sequences

Let $F_m$ be the Fibonacci
numbers, extended to all integers $m$ by $F_{m+2} = F_{m+1} + F_m$, and let $G$ and $H$ be
gibonacci sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with
$X_{j+2} = X_{j+1} + X_j$ for every integer $j$. Then for all integers $k$, $r$, $s$, $t$,

$$
G_{k+s-r} H_{k+r+t} + G_{k+s+r} H_{k-r+t} =
2 G_{k+s} H_{k+t} +
(-1)^{k+r} F_r^2 \bigl(G_0 (H_{s+t} + H_{s+t-2}) + G_1 (H_{s+t+1} + H_{s+t-1})\bigr) -
(-1)^{k+r} F_r^2 (G_{s+1} + G_{s-1}) (H_{t+1} + H_{t-1}).
$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 45 (`jis-2024-24.6.2-prop-45`).
