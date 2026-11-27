# Lucas-weighted identity for two gibonacci sequences

Let $F_m$ be the Fibonacci numbers
extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$) and
$L_m = F_{m-1} + F_{m+1}$ the Lucas numbers, and let $G, H \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for
all integers $r$, $s$, $t$,

$$L_r (G_0 H_{s+t-1} + G_1 H_{s+t}) - (-1)^r G_{s-r} (H_{t+1} + H_{t-1})
= H_{r+t} (G_{s+1} + G_{s-1}).$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 44 (`jis-2024-24.6.2-prop-44`).
