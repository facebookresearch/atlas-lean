# Counting permutations by mesh-pattern matches

Let $2 \le k \le n$ and let $j$ be a
natural number. For a permutation $\sigma$ of $\{1, \dots, n\}$, let $p$ be the position of its
largest entry, and call a position $i$ a match if $\sigma(t) < \sigma(i)$ for every position
$t < i$ and at least $k - 1$ positions $q$ with $i < q < p$ have $\sigma(q) > \sigma(i)$. Let
$N(\sigma)$ be the number of matches, plus $1$ if $p \ge k$. Then the number of permutations
$\sigma$ of $\{1, \dots, n\}$ with $N(\sigma) = j$ equals $(k-1)!\, c_{k-1}(n, j + k - 1)$, where
the unsigned $r$-Stirling number of the first kind $c_r(n, m)$ is the coefficient of $X^m$ in
$X^r (X + r)(X + r + 1) \cdots (X + n - 1)$.

## Sources

- Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers", Journal of Integer Sequences 18 (2015), Article 15.10.1, Theorem `thm:rstir`, line 201, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.
