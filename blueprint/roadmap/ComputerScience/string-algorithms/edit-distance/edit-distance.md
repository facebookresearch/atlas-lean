# Edit distance algorithm

Given lists $s = s_1 \cdots s_m$ and $t = t_1 \cdots t_n$ over a
type with a Boolean equality test, the algorithm fills a table $D(i, j)$ for $0 \le i \le m$ and
$0 \le j \le n$ by $D(0, j) = j$, $D(i, 0) = i$ and
$D(i, j) = \min(D(i-1, j-1) + c_{ij}, D(i-1, j) + 1, D(i, j-1) + 1)$ for $i, j \ge 1$,
where $c_{ij}$ is $0$ if the test reports $s_i = t_j$ and $1$ otherwise. It then walks back
from $(m, n)$ to $(0, 0)$: on the boundary it deletes the remaining $s_i$ or inserts the
remaining $t_j$; otherwise it takes a move attaining the minimum, preferring the diagonal move
(a keep of $s_i$ if the test reports $s_i = t_j$, else a substitution of $t_j$ for $s_i$),
then a deletion of $s_i$, then an insertion of $t_j$. It returns the distance $D(m, n)$
together with the edit script of the chosen moves in left-to-right order. Each of the
$(m + 1)(n + 1)$ table entries is charged as one cell transition and each emitted operation
as one reconstruction step.
