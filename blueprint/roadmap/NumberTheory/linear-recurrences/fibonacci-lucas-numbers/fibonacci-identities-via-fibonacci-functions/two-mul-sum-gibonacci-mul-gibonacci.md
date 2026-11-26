# Sum of products of two gibonacci sequences

Let $G, H \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. For every
natural number $n$ and all integers $k$ and $s$,

$$2 \sum_{j=1}^{n} G_{j+k} H_{j+s} = G_{n+k} H_{n+s+1} + G_{n+k+1} H_{n+s} -
G_{k+1} H_s - G_k H_{s+1}.$$

The printed statement lacks the factor $2$: it fails for the Fibonacci sequence $G = H = F$
with $k = s = 0$ and $n = 1$, where the left side is $1$ and the right side $2$. The paper's own
derivation (its display before the proposition) carries the factor $2$.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 30 (`jis-2024-24.6.2-prop-30`).
