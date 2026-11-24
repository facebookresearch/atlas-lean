# Levels of a sparse table

For a list $a$ over a type with a minimum operation $\min$, the
levels of $a$ are defined recursively: level $0$ is $a$, and if level $k$ is
$\ell = (\ell_0, \dots, \ell_{m-1})$, then level $k + 1$ is the list of the values
$\min(\ell_i, \ell_{i+2^k})$ for $0 \le i < m - 2^k$ (empty when $m \le 2^k$).

Over a linear order, element $i$ of level $k$ is the minimum of the $2^k$ consecutive elements
of $a$ starting at index $i$, and only start indices whose interval fits in $a$ get an element.
