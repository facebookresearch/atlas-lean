# The KMP failure function

Let $p$ be a pattern of length $n$ over a type with a lawful
boolean equality, and write $p_{\lt k}$ for its prefix of length $k$. Each entry of the KMP prefix
table of $p$ pairs a symbol of $p$ with a failure value. For every $q < n$, the failure value
$f$ of entry $q$ (counting from $0$) is the length of the longest proper prefix of $p_{\lt q+1}$
that is also a suffix of $p_{\lt q+1}$: $f \le q$, $p_{\lt f}$ is a suffix of $p_{\lt q+1}$, and every
$k \le q$ such that $p_{\lt k}$ is a suffix of $p_{\lt q+1}$ satisfies $k \le f$.
