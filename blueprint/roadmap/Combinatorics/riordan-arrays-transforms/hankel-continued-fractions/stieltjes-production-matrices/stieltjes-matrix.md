# Tridiagonal Stieltjes production matrix

Let $R$ be an additive monoid with one and let
$a_1, b_1, a, b \in R$. The Stieltjes matrix $S$ is the infinite matrix with rows and columns
indexed by $\mathbb{N} = \{0, 1, 2, \dots\}$ whose entries are $S_{i, i+1} = 1$ for every $i$,
$S_{0,0} = a_1$, $S_{1,0} = b_1$, $S_{i,i} = a$ and $S_{i+1,i} = b$ for every $i \ge 1$, and
$S_{i,j} = 0$ for all other $i, j$. So row $0$ is $a_1, 1, 0, \dots$, row $1$ is
$b_1, a, 1, 0, \dots$, and each row $i \ge 2$ has $b$ below the diagonal, $a$ on the diagonal, $1$
above the diagonal and $0$ elsewhere.
