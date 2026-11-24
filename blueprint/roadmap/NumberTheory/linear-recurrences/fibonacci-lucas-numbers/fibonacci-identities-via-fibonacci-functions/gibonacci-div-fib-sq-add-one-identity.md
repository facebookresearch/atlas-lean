# Gibonacci identity with Fibonacci-square denominators

Let $G : \mathbb{Z} \to \mathbb{R}$,
written $j \mapsto G_j$, satisfy $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $r$ and $k$,

$$
\frac{G_{r+2}}{F_{2k}^2 + 1} - \frac{G_r}{F_{2k+2}^2 + 1} =
\frac{G_{2k+r+3} + G_{2k+r+1}}{F_{2k+1} (F_{2k+1}^2 + 1)} - \frac{G_{r+1}}{F_{2k+1}^2 + 1}.
$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 46 (`jis-2024-24.6.2-prop-46`).
