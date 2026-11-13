# Four-sequence Candido-type identity for gibonacci sequences

Let $G$, $H$, $M$, $N$ be
gibonacci sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with
$X_{j+2} = X_{j+1} + X_j$ for every integer $j$. For two such sequences $X$, $Y$ and integers
$x$, $y$ write $T(X, x; Y, y) = X_x Y_y + X_{x+1} Y_{y+1} + X_{x+2} Y_{y+2}$. Then for all
integers $k$, $r$, $s$, $t$,

$$
6 (G_k H_r M_s N_t + G_{k+1} H_{r+1} M_{s+1} N_{t+1} + G_{k+2} H_{r+2} M_{s+2} N_{t+2}) =
T(G, k; M, s) \, T(H, r; N, t) + T(G, k; H, r) \, T(M, s; N, t) +
T(G, k; N, t) \, T(H, r; M, s).
$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 38 (`jis-2024-24.6.2-prop-38`).
