# Invariant of the LIS table

A table $t$ of triples $(y, k, zs)$ satisfies the invariant for
a list $l$ when every entry $(y, k, zs)$ of $t$ has a list $s$ such that $y$ followed by $s$ is a
suffix of $l$ and $(k, zs)$ is a table cell for $y$ followed by $s$, and conversely, for every
element $y$ and list $s$ such that $y$ followed by $s$ is a suffix of $l$, some entry $(y, k, zs)$
of $t$ makes $(k, zs)$ a table cell for $y$ followed by $s$.
