# The KMP failure function

Let $p$ be a pattern of length $n$ over a type with a Boolean
equality test that agrees with equality, and write $p_{\lt k}$ for its prefix of length $k$. Each entry of the KMP prefix
table of $p$ pairs a symbol of $p$ with a failure value. For every $q < n$, the failure value
$f$ of entry $q$ (counting from $0$) is the length of the longest proper prefix of $p_{\lt q+1}$
that is also a suffix of $p_{\lt q+1}$: $f \le q$, $p_{\lt f}$ is a suffix of $p_{\lt q+1}$, and every
$k \le q$ such that $p_{\lt k}$ is a suffix of $p_{\lt q+1}$ satisfies $k \le f$.

In the notation of the paper, which numbers pattern positions from $1$ and defines $f[j]$ as the
largest $i < j$ such that $p[1] \dots p[i-1]$ is a suffix of $p[1] \dots p[j-1]$, the failure value
of entry $q$ is $f[q + 2] - 1$. For the paper's example pattern $abcabcacab$, with
$f[1], \dots, f[10] = 0, 1, 1, 1, 2, 3, 4, 5, 1, 2$, the failure values of entries $0$ to $8$
are $0, 0, 0, 1, 2, 3, 4, 0, 1$ (entry $9$ would need $f[11]$, which the paper's table does not
list).

## Sources

- D. E. Knuth, J. H. Morris, Jr. and V. R. Pratt, "Fast pattern matching in strings", *SIAM J.
  Comput.* 6(2) (1977) 323–350, DOI 10.1137/0206024, Section 2, definition of $f[j]$.
