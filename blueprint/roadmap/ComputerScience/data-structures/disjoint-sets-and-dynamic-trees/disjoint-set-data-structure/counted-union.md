# Union by rank with operation counts

For a union-find structure $S$ and indices $x, y$
of $S$, this computation runs counted FIND on $x$ in $S$, giving a structure $S_1$ and a root
$r_x$; then counted FIND on $y$ in $S_1$, giving a structure $S_2$ and a root $r_y$; then counted
linking of $r_x$ and $r_y$ in the node array of $S_2$. It returns the array produced by the
linking, with cost $((a, b), (t, p, w))$, where $a$ and $b$ are the total numbers of root tests
and parent writes of the two FIND calls, and $(t, p, w)$ counts the rank tests, parent writes and
rank writes of the linking.
