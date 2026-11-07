# Morphic coding of the Wythoff mex pairs at level one

Let $a_n$ be the least natural
number $m > 1$ that differs from $a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 2$,
so that $(a_0, b_0) = (2, 4)$. Let $f_1$ be the morphism on the alphabet $\{0, 1, 2, 3, 4\}$
given by $0 \mapsto 0\,1$, $1 \mapsto 2$, $2 \mapsto 3\,4$, $3 \mapsto 3\,1$, $4 \mapsto 2$ and
extended to finite words by concatenation, and let $g_1$ send the letters $0, 1, 3$ to $a$ and
the letters $2, 4$ to $b$. Then there is an infinite word $w = w(0)\,w(1)\,w(2) \cdots$ over this
alphabet that is the limit of the iterates $f_1^k(0)$ (each $f_1^k(0)$ is a prefix of $w$, and
their lengths are unbounded), and for every such $w$ and every $n \ge 0$, $g_1(w(a_n - 2)) = a$
and $g_1(w(b_n - 2)) = b$.

By Theorem 17 of the source, the pairs $(a_n, b_n)$ and $(b_n, a_n)$ are the non-terminal
P-positions of $K^1$, Wythoff's game in which no move is allowed from a position $(x, y)$ with
$x + y \le 1$; indexing the letters of $w$ from $2$, the letter at $a_n$ is coded $a$ and the
letter at $b_n$ is coded $b$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Proposition 22 (`jis-2026-26.1.6-prop-22`).
