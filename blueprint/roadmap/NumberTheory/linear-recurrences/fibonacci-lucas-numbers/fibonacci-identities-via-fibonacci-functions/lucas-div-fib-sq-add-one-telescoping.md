# Two telescoping relations between Lucas and Fibonacci numbers

Let $F_m$ be the Fibonacci
numbers extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$) and
$L_m = F_{m-1} + F_{m+1}$ the Lucas numbers. Then for every integer $k$,

$$\frac{L_{2k+1}}{F_{2k+1}^2 + 1} = \frac{L_{2k}}{F_{2k}^2 + 1} - \frac{L_{2k+2}}{F_{2k+2}^2 + 1}$$

and

$$\frac{L_{2k+1}}{L_{2k} L_{2k+2}} \cdot \frac{(F_{2k}^2 + 1)(F_{2k+2}^2 + 1)}{F_{2k+1}^2 + 1}
= \frac{F_{2k+2}^2 + 1}{L_{2k+2}} - \frac{F_{2k}^2 + 1}{L_{2k}}.$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 3 (`jis-2024-24.6.2-prop-3`).
