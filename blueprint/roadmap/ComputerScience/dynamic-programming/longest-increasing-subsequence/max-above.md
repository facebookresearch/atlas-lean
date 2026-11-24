# Best table entry above a value

Given a value $x$ and a list $t$ of entries $(y, k, zs)$,
where $y$ is a value, $k$ a natural number and $zs$ a list of values, this timed computation
returns the pair of $k$ and the list $y$ followed by $zs$ for an entry of $t$ with $x < y$ whose
$k$ is largest among such entries, provided that $k$ is positive; if no entry with $x < y$ has
$k > 0$, it returns $0$ and the empty list. It costs one unit per entry of $t$.
