# Diagonal sums of an array

For a doubly indexed array $(a_{i,j})_{i, j \ge 0}$ with entries
in an additive commutative monoid $M$, the $n$-th diagonal sum is
$d_n = \sum_{i + j = n} a_{i,j} = \sum_{k=0}^{n} a_{k,n-k}$.

If $a$ is a lower-triangular array with $a_{i,j}$ in row $i$ and column $j$, these are its sums
along rising diagonals. For a Riordan array $(g, f)$, whose column $j$ has generating function
$g(x) f(x)^j$, the sequence $(d_n)$ has generating function $g(x) / (1 - x f(x))$.
