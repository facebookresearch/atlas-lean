# Howard's formula for the series $\sum_{k \ge 0} 2x^k/(k+2)!$

Let $n$ be a natural
number, let

$$h(x) = \sum_{k \ge 0} \frac{2}{(k+2)!}\, x^k \in \mathbb{Q}[[x]],$$

let $h^{-1}$ be its inverse in $\mathbb{Q}[[x]]$, and write $[x^n]\, f$ for the coefficient of
$x^n$ in a power series $f$. Let $G_n \in \mathbb{Q}[X]$ be a polynomial of degree at most $n$
such that $G_n(m) = n!\, [x^n]\, (h^{-1})^m$ for every natural number $m \le n$. Then

$$G_n(X) = \sum_{i=0}^{n} (-1)^i\, 2^i\, \frac{n!\, i!}{(n+2i)!} \cdot
\frac{X(X+1)\cdots(X+i-1)}{i!} \cdot \frac{(X+n)(X+n-1)\cdots(X+i+1)}{(n-i)!} \cdot
B_{n+2i,\,i}(0, 1, 1, \dots),$$

where empty products equal $1$ and $B_{n+2i,\,i}(0, 1, 1, \dots)$ is the partial Bell
polynomial evaluated at the sequence whose first term is $0$ and whose other terms are all $1$.

## Sources

- G. Nemes, Journal of Integer Sequences 13 (2010), https://cs.uwaterloo.ca/journals/JIS/VOL13/Nemes/nemes2.tex, lines 120-133 (generic) and 166-173 (specialization).
