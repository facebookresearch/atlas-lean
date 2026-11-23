# Overlap statistic on pairs of words

Fix natural numbers $k$, $n \ge 1$, $r \ge 1$ and a
rational number $q$. For words $u$ and $v$ over an alphabet of $k$ letters, the overlap of
$(u, v)$ is the number of positions of $v$ whose letter occurs in $u$. Write $[x^m] F$ for the
coefficient of $x^m$ in a formal power series $F$ over $\mathbb{Q}$, $S(m, j)$ for the Stirling
numbers of the second kind, and $c_j = qj + k - j$. Then the sum of $q^{\text{overlap}}$ over all
pairs $(u, v)$ with $u$ of length $n$ and $v$ of length $r$ equals
$\sum_{j=1}^{k} \binom{k}{j} \, [x^r]\bigl(c_j x \, (1 - c_j x)^{-1}\bigr) \, j! \, S(n, j)$.

## Sources

- Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024), Article A107, Theorem 2.
