# Kolakoski sequences

A sequence $K_1, K_2, K_3, \ldots$ of natural numbers is a Kolakoski
sequence when $K_1 = 1$, every $K_n$ with $n \ge 1$ is $1$ or $2$, and $K$ describes its own runs
in the following sense. Let $s_1 = 1$ and $s_{n+1} = s_n + K_n$ for $n \ge 1$, and call block $n$
the set of positions $i$ with $s_n \le i < s_n + K_n$. For every $n \ge 1$, every term $K_i$ with
$i$ in block $n$ equals $1$ if $n$ is odd and $2$ if $n$ is even.

The sequence is indexed from $1$; its value at index $0$ is unconstrained.
