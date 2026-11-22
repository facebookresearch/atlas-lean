# Table of the quadratic LIS program

The table of a list is a list of triples $(y, k, zs)$,
built from the right: the empty list has the empty table, and the table of $x$ followed by $rest$
is the table $t$ of $rest$ with the entry $(x, b + 1, w)$ put in front, where $(b, w)$ is the
result of the scan of $t$ for entries above $x$. Building the table costs the total cost of these
scans.
