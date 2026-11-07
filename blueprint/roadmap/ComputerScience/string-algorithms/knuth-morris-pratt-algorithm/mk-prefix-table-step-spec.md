# Correctness of the KMP transition

Let $p$ be a pattern of length $n$ over a type with
a lawful boolean equality, and write $p_{\lt k}$ for its prefix of length $k$. Let $c$ be a list,
$x$ a symbol, and $cx$ the list $c$ followed by $x$. Suppose the state $s \le n$ is the length
of the longest prefix of $p$ that is a suffix of $c$: $p_{\lt s}$ is a suffix of $c$, and every
$k \le n$ such that $p_{\lt k}$ is a suffix of $c$ satisfies $k \le s$. Then the state $s'$ that
the transition of the KMP prefix table of $p$ produces from $s$ on reading $x$ is the length of
the longest prefix of $p$ that is a suffix of $cx$: $s' \le n$, $p_{\lt s'}$ is a suffix of $cx$,
and every $k \le n$ such that $p_{\lt k}$ is a suffix of $cx$ satisfies $k \le s'$.
