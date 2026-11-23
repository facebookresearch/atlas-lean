# Table cell of the LIS dynamic program

For an element $x$, lists $s$ and $zs$, and a
natural number $k$, the pair $(k, zs)$ is a table cell for $x$ followed by $s$ when $zs$ is a
subsequence (not necessarily contiguous) of $s$, the list $x$ followed by $zs$ is strictly
increasing (each element strictly less than every later one) and has length $k$, and for every
subsequence $zs'$ of $s$ such that $x$ followed by $zs'$ is strictly increasing, the list $x$
followed by $zs'$ has length at most $k$. So $x$ followed by $zs$ is a longest strictly increasing
subsequence of $x$ followed by $s$ that starts with this $x$.
