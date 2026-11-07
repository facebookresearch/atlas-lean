# Counting strongly restricted permutations with displacements $-m$, $0$, $jm$

Let
$m, j, i, r$ be natural numbers with $j \ge 1$ and $r < m$, and let $F_j$ be the Fibonacci
$j$-numbers: $F_j(0) = 0$, $F_j(n) = 1$ for $1 \le n \le j$, and
$F_j(n) = F_j(n-1) + F_j(n-j-1)$ for $n > j$. Then the number of permutations $\pi$ of
$\{0, 1, \dots, im + r - 1\}$ such that $\pi(x) - x \in \{-m, 0, jm\}$ for every $x$ equals
$F_j(i+1)^{m-r} \, F_j(i+2)^r$.

In the paper's notation this is
$P^{\{-m,0,jm\}}_{im+r} = (f^{(j+1)}_i)^{m-r} (f^{(j+1)}_{i+1})^r$, where the
$(1,t)$-bonacci numbers $f^{(t)}_n$ satisfy $f^{(j+1)}_n = F_j(n+1)$.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Corollary 14.
