# Morphic coding of the Wythoff mex pairs at level three

Let $a_n$ be the least integer
$m > 3$ that differs from $a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 4$, so that
$(a_0, b_0) = (4, 8)$. Let $f_3$ be the morphism on the alphabet $\{0, 1, \dots, 21\}$ given by
$0 \mapsto 0\,1$, $1 \mapsto 2$, $2 \mapsto 3\,4$, $3 \mapsto 5\,6$, $4 \mapsto 7$,
$5 \mapsto 8\,9$, $6 \mapsto 10$, $7 \mapsto 11\,12$, $8 \mapsto 13\,12$, $9 \mapsto 14$,
$10 \mapsto 15\,16$, $11 \mapsto 14\,17$, $12 \mapsto 18$, $13 \mapsto 14\,17$,
$14 \mapsto 19\,12$, $15 \mapsto 18\,20$, $16 \mapsto 21$, $17 \mapsto 18$, $18 \mapsto 13\,12$,
$19 \mapsto 19\,12$, $20 \mapsto 14$, $21 \mapsto 15\,16$ and extended to finite words by
concatenation, and let $g_3$ send the letters $4, 6, 8, 10, 13, 15, 17, 19, 20$ to $b$ and every
other letter to $a$. Then there is an infinite word $w = w(0)\,w(1)\,w(2) \cdots$ over this
alphabet that is the limit of the iterates $f_3^k(0)$ (each $f_3^k(0)$ is a prefix of $w$, and
their lengths are unbounded), and for every such $w$ and every $n \ge 0$,
$g_3(w(a_n - 4)) = a$ and $g_3(w(b_n - 4)) = b$.

By Theorem 17 of the source, the pairs $(a_n, b_n)$ and $(b_n, a_n)$ are the non-terminal
P-positions of $K^3$, Wythoff's game in which no move is allowed from a position $(x, y)$ with
$x + y \le 3$; indexing the letters of $w$ from $4$, the letter at $a_n$ is coded $a$ and the
letter at $b_n$ is coded $b$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Proposition 24 (`jis-2026-26.1.6-prop-24`).
