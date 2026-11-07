# Blocking Wythoff Nim with one or two blocked options has no redundant move

Let
$\varphi$ be the golden ratio. Let $R_2$ consist of $(0, 0)$ and, for every $n \ge 0$, the
positions $(n, 2n + 1)$, $(2n + 1, n)$,
$(2\lfloor n\varphi \rfloor + 2, 2\lfloor n\varphi^2 \rfloor + 2)$ and
$(2\lfloor n\varphi^2 \rfloor + 2, 2\lfloor n\varphi \rfloor + 2)$, and let $R_3$ consist of
$(0, 0)$ and, for every $n \ge 0$, the positions $(n, 2n + 1)$, $(2n + 1, n)$, $(n, 2n + 2)$ and
$(2n + 2, n)$. A Wythoff move from a position $x$ of two piles to a position $y$ removes a
positive number of tokens from one pile, or the same positive number from both. Let $v$ be
$(i, 0)$, $(0, i)$ or $(i, i)$ for an integer $i > 0$. Then some position $x \notin R_2$ has
fewer than two Wythoff moves to positions $y \in R_2$ with $y + v \ne x$, and some position
$x \notin R_3$ has fewer than three Wythoff moves to positions $y \in R_3$ with $y + v \ne x$.

So once the moves by $v$ are removed, $R_2$ and $R_3$ are no longer the sets of P-positions of
$W^2$ and $W^3$, Wythoff's game in which the previous player may forbid one, respectively two,
options.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 31 (`jis-2026-26.1.6-thm-31`).
