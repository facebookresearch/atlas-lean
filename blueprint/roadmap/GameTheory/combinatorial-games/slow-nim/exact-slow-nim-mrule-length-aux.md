# Fuel-bounded length of M-rule play

Let $k$ and $f$ be natural numbers and let $x$ be a
position on $k + 1$ piles. Call $x$ terminal when $k = 0$ or fewer than $k$ of its piles are
nonempty. The value at $f$ and $x$ is $0$ when $f = 0$ or $x$ is terminal; otherwise it is $1$
plus the value at $f - 1$ and the position reached from $x$ by the M-move. Thus it counts the
M-moves played from $x$, stopping at a terminal position or after $f$ moves.

## Sources

- Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Section 1.2 (the function `M`).
