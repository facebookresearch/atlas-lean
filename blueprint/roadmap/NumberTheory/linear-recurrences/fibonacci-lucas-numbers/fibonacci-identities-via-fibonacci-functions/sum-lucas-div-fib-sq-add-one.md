# Telescoping sums of Lucas numbers over Fibonacci squares plus one

Let $F_m$ denote the
Fibonacci numbers and $L_m$ the Lucas numbers ($L_0 = 2$, $L_1 = 1$, $L_{m+2} = L_{m+1} + L_m$).
For every natural number $n$,

$$\sum_{k=1}^{n} \frac{L_{2k+1}}{F_{2k+1}^2 + 1} = \frac{3}{2} - \frac{L_{2n+2}}{F_{2n+2}^2 + 1}$$

and

$$\sum_{k=1}^{n} \frac{L_{2k+1}}{L_{2k} L_{2k+2}} \cdot
\frac{(F_{2k}^2 + 1)(F_{2k+2}^2 + 1)}{F_{2k+1}^2 + 1} =
\frac{F_{2n+2}^2 + 1}{L_{2n+2}} - \frac{2}{3},$$

and the real series $\sum_{k \ge 1} L_{2k+1} / (F_{2k+1}^2 + 1)$ has sum $3/2$.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 4 (`jis-2024-24.6.2-prop-4`).
