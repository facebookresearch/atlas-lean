# The FIND phases of a union make two more root tests than parent writes

For a
union-find structure $S$ and indices $x, y$ of $S$, in the counted union of $x$ and $y$ in $S$ the
total number of root tests made by its two FIND calls equals the total number of parent writes
they make plus $2$.
