# Larsson's P-positions of Blocking Wythoff Nim with one blocked option

Let $\varphi$ be
the golden ratio, and let $R_2$ consist of $(0, 0)$ and, for every $n \ge 0$, the positions
$(n, 2n + 1)$, $(2n + 1, n)$, $(2\lfloor n\varphi \rfloor + 2, 2\lfloor n\varphi^2 \rfloor + 2)$
and $(2\lfloor n\varphi^2 \rfloor + 2, 2\lfloor n\varphi \rfloor + 2)$. A Wythoff move from a
position of two piles removes a positive number of tokens from one pile, or the same positive
number from both. Then every position in $R_2$ has at most one Wythoff move to a position in
$R_2$, and every position outside $R_2$ has at least two Wythoff moves to positions in $R_2$.

Hence $R_2$ is the set of P-positions of $W^2$, Wythoff's game in which the previous player may
forbid one option.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 26 (`jis-2026-26.1.6-thm-26`).
