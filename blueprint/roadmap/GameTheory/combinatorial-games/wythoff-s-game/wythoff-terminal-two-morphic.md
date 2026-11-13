# Morphic coding of the Wythoff mex pairs at level two

Let $a_n$ be the least integer
$m > 2$ that differs from $a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 3$, so that
$(a_0, b_0) = (3, 6)$. Let $f_2$ be the morphism on the alphabet $\{0, 1, \dots, 15\}$ given by
$0 \mapsto 0\,1$, $1 \mapsto 2$, $2 \mapsto 3\,4$, $3 \mapsto 5\,6$, $4 \mapsto 7$,
$5 \mapsto 8\,9$, $6 \mapsto 10$, $7 \mapsto 11\,12$, $8 \mapsto 10\,13$, $9 \mapsto 14$,
$10 \mapsto 10\,13$, $11 \mapsto 5\,6$, $12 \mapsto 15$, $13 \mapsto 5$, $14 \mapsto 8\,9$,
$15 \mapsto 11\,12$ and extended to finite words by concatenation, and let $g_2$ send the
letters $3, 5, 7, 10$ to $b$ and every other letter to $a$. Then there is an infinite word
$w = w(0)\,w(1)\,w(2) \cdots$ over this alphabet that is the limit of the iterates $f_2^k(0)$
(each $f_2^k(0)$ is a prefix of $w$, and their lengths are unbounded), and for every such $w$
and every $n \ge 0$, $g_2(w(a_n - 3)) = a$ and $g_2(w(b_n - 3)) = b$.

By Theorem 17 of the source, the pairs $(a_n, b_n)$ and $(b_n, a_n)$ are the non-terminal
P-positions of $K^2$, Wythoff's game in which no move is allowed from a position $(x, y)$ with
$x + y \le 2$; indexing the letters of $w$ from $3$, the letter at $a_n$ is coded $a$ and the
letter at $b_n$ is coded $b$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Proposition 23 (`jis-2026-26.1.6-prop-23`).
