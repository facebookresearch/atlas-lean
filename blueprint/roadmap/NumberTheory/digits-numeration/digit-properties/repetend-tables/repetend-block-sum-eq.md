# Block sums of a repetend

Let $B \ge 2$, $N$, $x < N$, $d \ge 1$ and $k \ge 1$ be natural
numbers, and let $a_i = \lfloor xB^{i+1}/N \rfloor \bmod B$ be the $i$-th base-$B$ digit of $x/N$.
Suppose $a_{i+dk} = a_i$ for every natural number $i$. Let
$S = \sum_{j\lt d} \sum_{i\lt k} a_{jk+i} B^{k-1-i}$ be the sum of the first $d$ blocks of $k$ digits,
each read as a base-$B$ number, and let $R = \sum_{j\lt d} (xB^{jk} \bmod N)$. Then
$SN = R(B^k - 1)$, and if $B^k - 1$ is coprime to $N$, then $B^k - 1$ divides $S$.

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Theorem 9.
