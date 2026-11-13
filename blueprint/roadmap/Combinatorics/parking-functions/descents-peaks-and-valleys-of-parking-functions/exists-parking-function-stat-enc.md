# Every statistic encoding comes from a parking function

Write a parking function $f$ of
length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its statistic encoding is
the word $w_1 \cdots w_{n-1}$ over the letters $A$, $D$, $T$ with $w_j = A$ if $a_j < a_{j+1}$
(an ascent), $w_j = D$ if $a_j > a_{j+1}$ (a descent) and $w_j = T$ if $a_j = a_{j+1}$ (a tie).
For every natural number $n$, every word of length $n - 1$ over $A$, $D$, $T$ (the empty word
when $n = 0$) is the statistic encoding of some parking function of length $n$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 48 (`jis-2024-24.8.6-thm-48`).
