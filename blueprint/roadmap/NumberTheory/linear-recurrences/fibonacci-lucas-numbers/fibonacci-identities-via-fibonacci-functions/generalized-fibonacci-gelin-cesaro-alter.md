# Alternating Gelin–Cesàro sum for generalized Fibonacci sequences

Let $p$ be a real
number, let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$ for every integer
$j$, and put $\gamma_W = (p W_0 W_1 + W_0^2 - W_1^2)(p^2 - 1)$. Let $n \ge 0$ and $k$ be
integers such that $W_{j+k-2} W_{j+k-1} W_{j+k+1} W_{j+k+2} \ne 0$ for $1 \le j \le n$ and
$W_{n+k-1}$, $W_{k-1}$, $W_{n+k+2}$, $W_{k+2}$ are nonzero. Then

$$
\sum_{j=1}^{n} \frac{(-1)^{j-1} \cdot 2 W_{j+k} (W_{j+k+1} + W_{j+k-1})
\bigl(2 W_{j+k}^2 + (-1)^{j+k} \gamma_W\bigr)}{W_{j+k-2} W_{j+k-1} W_{j+k+1} W_{j+k+2}} =
(-1)^{n+1} \frac{W_{n+k} + W_{n+k-2}}{W_{n+k-1}} + \frac{W_k + W_{k-2}}{W_{k-1}} +
(-1)^{n+1} \frac{W_{n+k+3} + W_{n+k+1}}{W_{n+k+2}} + \frac{W_{k+3} + W_{k+1}}{W_{k+2}}.
$$

The paper's standing assumption $p \ne 0$ is not needed.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 11 (`jis-2024-24.6.2-prop-11`).
