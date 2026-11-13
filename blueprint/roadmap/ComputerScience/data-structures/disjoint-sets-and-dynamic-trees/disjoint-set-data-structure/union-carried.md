# Union unfolds to two finds and a link

Let $U$ be a union-find structure on
$\{0, \dots, n-1\}$ and let $x, y < n$. Run find with path compression on $x$ in $U$, giving a
structure $U_1$ and a root $r_x$; then run find on $y$ in $U_1$ (not in $U$), giving a structure
$U_2$ and a root $r_y$. Then the node array of the union of $x$ and $y$ in $U$ equals the array
obtained from the node array of $U_2$ by linking $r_x$ and $r_y$ by rank: nothing changes if
$r_x = r_y$; otherwise, if $\operatorname{rank}(r_y) < \operatorname{rank}(r_x)$ then $r_y$ gets
parent $r_x$, and if not then $r_x$ gets parent $r_y$ and, when the two ranks are equal, the rank
of $r_y$ increases by one.
