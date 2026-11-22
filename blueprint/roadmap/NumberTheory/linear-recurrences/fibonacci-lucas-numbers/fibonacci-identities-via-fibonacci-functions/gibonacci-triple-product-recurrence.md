# Product recurrence for three gibonacci sequences

Let
$G, H, I : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$, $j \mapsto H_j$ and
$j \mapsto I_j$, satisfy $G_{j+2} = G_{j+1} + G_j$, $H_{j+2} = H_{j+1} + H_j$ and
$I_{j+2} = I_{j+1} + I_j$ for every integer $j$. Then for all integers $k$, $r$ and $s$,

$$
G_{k+1} H_{r+1} I_{s+1} = 3 G_k H_r I_s + 6 G_{k-1} H_{r-1} I_{s-1} -
3 G_{k-2} H_{r-2} I_{s-2} - G_{k-3} H_{r-3} I_{s-3}.
$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 25 (`jis-2024-24.6.2-prop-25`).
