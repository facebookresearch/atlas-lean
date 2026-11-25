# Sentinel list insertion (LIST-INSERT′)

Let $S$ be a store of $n$ cells, each empty or
holding a node, in which the cells $x$ and $y$ are allocated, the next pointer of $y$ is not
NIL, and the cell $w$ it points to is allocated. Sentinel insertion of $x$ after $y$ performs four
pointer assignments in order, each costing one time unit, and returns the resulting store: set
the next pointer of $x$ to the next pointer of $y$; set the previous pointer of $x$ to $y$; set
the previous pointer of the successor $w$ of $y$ to $x$; set the next pointer of $y$ to $x$.

Each assignment reads the store left by the previous ones, so aliased cells see earlier writes.
Unlike LIST-INSERT, there is no NIL test.
