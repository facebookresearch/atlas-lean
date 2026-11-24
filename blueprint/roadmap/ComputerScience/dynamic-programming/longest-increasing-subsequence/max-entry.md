# Table entry of largest length

Given a list $t$ of entries $(y, k, zs)$, where $k$ is a
natural number and $zs$ is a list with elements of the same type as $y$, this timed computation
returns the pair of $k$ and the list $y$ followed by $zs$ for an entry of $t$ whose $k$ is
largest, provided that this $k$ is positive, and returns $0$ and the empty list otherwise (in
particular when $t$ is empty). It costs one unit per entry of $t$.
