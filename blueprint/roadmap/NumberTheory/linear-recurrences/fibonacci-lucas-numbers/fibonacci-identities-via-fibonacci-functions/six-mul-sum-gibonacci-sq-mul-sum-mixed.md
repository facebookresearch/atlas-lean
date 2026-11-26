# Mixed Melham-type sum for two gibonacci sequences

Let $F_m$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$), and let $G, H \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for
every natural number $n$ and all integers $k$, $r$,

$$6 \Bigl(\sum_{j=0}^{2n-1} G_{k+j}^2\Bigr) \Bigl(\sum_{j=0}^{2n-1} H_{r+j} G_{k+j}\Bigr)
= F_{2n}^2 \bigl(H_{r+n-2} G_{k+n-2}^3 + 4 H_{r+n-1} G_{k+n-1}^3 +
4 H_{r+n} G_{k+n}^3 + H_{r+n+1} G_{k+n+1}^3\bigr).$$

The paper leaves $n$ unquantified; it is taken as a natural number, as in
Proposition 8.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 33 (`jis-2024-24.6.2-prop-33`).
