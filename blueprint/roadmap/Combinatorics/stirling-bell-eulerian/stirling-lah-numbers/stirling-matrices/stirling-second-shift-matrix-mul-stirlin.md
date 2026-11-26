# Inverting the shifted Stirling matrix $S^{[m]}(n)$

For a natural number $n$, let $V(n)$ be the $n \times n$ rational matrix, with rows and columns indexed by $1, \dots, n$, whose entries are $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$ and $0$ elsewhere, and let $\tilde V(n)$ be the upper triangular matrix with $\tilde V(n)_{i,j} = (-1)^{j-i} (i-1)!/j!$ for $j \ge i$ and $\tilde V(n)_{i,j} = 0$ for $j < i$. Let $s(n)$ be the $n \times n$ rational matrix with entries $s(i,j)$, the signed Stirling numbers of the first kind, and let $S^{[m]}(n)$ be the $n \times n$ rational matrix with entries $S(i+m, j)$, where $S(i,j)$ denotes the Stirling numbers of the second kind, all indices running over $1, \dots, n$. Then for all natural numbers $m$ and $n$,

$$S^{[m]}(n)\, \tilde V(n)^m\, s(n) = I_n.$$
