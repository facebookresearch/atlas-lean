# Alternating Fibonacci and Lucas sums from the Gelin–Cesàro identity

Let $F_m$ and $L_m$
denote the Fibonacci and Lucas numbers. For every natural number $n$,

$$
\sum_{k=1}^{n} \frac{(-1)^{k-1} F_{k+2}^2 F_{2k+4}}{F_{k+2}^4 - 1}
= \frac{5}{6} + \frac{(-1)^{n+1}}{2} \left(\frac{F_{2n+3}}{F_{n+1} F_{n+2}} -
\frac{F_{2n+5}}{F_{n+2} F_{n+3}} + \frac{F_{2n+7}}{F_{n+3} F_{n+4}}\right)
$$

and

$$
\sum_{k=1}^{n} \frac{(-1)^{k-1} L_{k+2}^2 F_{2k+4}}{L_{k+2}^4 - 25}
= \frac{5}{14} + \frac{(-1)^{n+1}}{2} \left(\frac{F_{2n+3}}{L_{n+1} L_{n+2}} -
\frac{F_{2n+5}}{L_{n+2} L_{n+3}} + \frac{F_{2n+7}}{L_{n+3} L_{n+4}}\right).
$$

The source's limiting cases are not included: the absolute values of the summands tend to
$\sqrt{5}$ and $1/\sqrt{5}$, so the summands do not tend to $0$ and neither series converges.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 10 (`jis-2024-24.6.2-prop-10`).
