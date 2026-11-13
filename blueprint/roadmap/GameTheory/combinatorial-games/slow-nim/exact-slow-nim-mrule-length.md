# M-rule length

Let $k$ be a natural number and let $x = (x_0, \dots, x_k)$ be a position
on $k + 1$ piles. Then $M(x)$ is the number of M-moves played from $x$ until a terminal position
(one with $k = 0$ or fewer than $k$ nonempty piles) is reached, computed as the fuel-bounded
length of M-rule play with fuel $x_0 + \dots + x_k$.

For $0 < k$ every M-move from a nonterminal position removes $k$ stones, so this much fuel
suffices and $M(x)$ is the full length of the M-rule play from $x$.

## Sources

- Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Section 1.2 (the function `M`).
