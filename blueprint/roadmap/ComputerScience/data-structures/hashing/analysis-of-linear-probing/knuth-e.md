# Knuth's auxiliary sums for linear probing

For natural numbers $r$, $N$ and $k$,

$$E_r(N, k) = \sum_{j=0}^{k-1} \binom{r + j}{r} \frac{(k-1)(k-2)\cdots(k-j)}{N^j},$$

the sums in which Knuth's 1963 note expresses the exact mean costs of linear probing. For $k = 0$
the sum is empty and equals $0$. For $k \ge 1$ and $N > 0$,

$$E_r(N, k) = 1 + \binom{r+1}{r}\frac{k-1}{N} + \binom{r+2}{r}\frac{(k-1)(k-2)}{N^2} + \cdots ;$$

for $N = 0$ and $k \ge 1$ the terms with $j \ge 1$ are $0$, by the convention that division by
zero gives $0$, so $E_r(0, k) = 1$. For $N > 0$, writing $\alpha = (k-1)/N$, each term is at most
$\binom{r+j}{r}\alpha^j$, so $E_r(N, k) \le (1-\alpha)^{-(r+1)}$ when $\alpha < 1$; this is the
approximation of Section 8 of the note.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 5, definition of $E_r(N, k)$: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
