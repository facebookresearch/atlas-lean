# An identity for products of two gibonacci sequences

Let
$G, H : \mathbb{Z} \to \mathbb{R}$ satisfy $G_{j+2} = G_{j+1} + G_j$ and
$H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for all integers $k$, $r$ and $s$,

$$
5 G_k H_{k+s-r} - \left(G_{k+1} + G_{k-1}\right) \left(H_{k+s-r+1} + H_{k+s-r-1}\right)
= 2 (-1)^{k-r+1} \left(G_{r+1} + G_{r-1}\right) \left(H_{s+1} + H_{s-1}\right) +
2 (-1)^{k-r} \left(G_0 \left(H_{r+s} + H_{r+s-2}\right) +
G_1 \left(H_{r+s+1} + H_{r+s-1}\right)\right).
$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 19 (`jis-2024-24.6.2-prop-19`).
