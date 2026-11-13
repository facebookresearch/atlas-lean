# Cost recurrence of the FIND auxiliary at a non-root

Let $S$ be a union-find structure
and $x < |S|$ a node whose parent $y$ in $S$ differs from $x$. If $c_x$ and $c_y$ are the costs
of the cost-counted FIND auxiliary on $x$ and on $y$, then $c_x = (1, 0) + (c_y + (0, 1))$:
one root test at $x$, then the run on $y$, then one parent write.
