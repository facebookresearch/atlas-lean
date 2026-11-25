# Hook length of a cell

For a cell $u = (i, j)$ of the Young diagram of $\lambda$, the hook of $u$ consists of $u$, the
cells to its right in row $i$ and the cells below it in column $j$. Its size is the hook length

$$h(i, j) = (\lambda_i - j) + (\lambda'_j - i) - 1,$$

with rows and columns indexed from $0$, $\lambda_i$ the length of row $i$ and $\lambda'_j$ that of
column $j$. The same expression is used for every pair $(i, j)$ of natural numbers, with truncated
subtraction (a negative difference counts as $0$); outside the diagram it has no combinatorial
meaning. For $\lambda = (4, 2, 2)$ the hook lengths are

$$\begin{matrix} 6 & 5 & 2 & 1 \\ 3 & 2 & & \\ 2 & 1 & & \end{matrix}$$

## Sources

- Richard P. Stanley, *Topics in Algebraic Combinatorics*, author's draft of 1 February 2013, https://math.mit.edu/~rstan/algcomb/algcomb.pdf (published as *Algebraic Combinatorics: Walks, Trees, Tableaux, and More*, Springer, 2013), Chapter 8, before Theorem 8.1.
