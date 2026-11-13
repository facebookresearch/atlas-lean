# Four-index product identity for two gibonacci sequences

Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $k$, $r$, $s$ and $t$,

$$
F_s (G_0 H_{k+r+t-1} + G_1 H_{k+r+t}) - (-1)^r F_{s-r} G_k (H_{t+1} + H_{t-1}) +
(-1)^r G_k H_{s-r+t} = G_{k+s} H_{r+t}.
$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 36 (`jis-2024-24.6.2-prop-36`).
