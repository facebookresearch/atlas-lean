# Golden-ratio formula for Wythoff's game with terminal positions up to total 3

Let
$\varphi$ be the golden ratio. Let $a_n$ be the least integer greater than $3$ that differs from
$a_i$ and $b_i$ for all $i < n$, and let $b_n = a_n + n + 4$. Then there is a Fibonacci-automatic
sequence $g_3 : \mathbb{N} \to \mathbb{N}$ with $g_3(n) \le 2$ for all $n$ such that, for every
$n \ge 0$, $a_n = \lfloor (n + 2)\varphi \rfloor + g_3(n + 1) - 1$ and
$b_n = \lfloor (n + 2)\varphi^2 \rfloor + g_3(n + 1) + 1$.

Here $(a_n, b_n)$ are the mex pairs of $K^3$, Wythoff's game in which every position $(x, y)$
with $x + y \le 3$ is terminal; by Theorem 17 of the source they are its non-terminal
P-positions with $a_n < b_n$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 13 (`jis-2026-26.1.6-thm-13`).
