# Count by terminal block

Let $n,m$ be natural numbers with $0 < m \le n$. The number $b(n,m)$ of Arndt compositions
of $n$ with last part $m$ is the sum of the contributions from a terminal singleton and a
terminal descending pair, respectively.

$$
b(n,m) =
\begin{cases} 1 & n=m, \\ F_{n-m-2} & \text{otherwise} \end{cases}
+
\begin{cases} 1 & n=2m+1, \\ F_{n-2m-1} & \text{otherwise} \end{cases}.
$$

Here $F_j$ is the Fibonacci number with $F_0=0$ and $F_1=1$, and subtraction in its index
is truncated at zero. At each terminal block's minimum weight, only the empty prefix occurs.
