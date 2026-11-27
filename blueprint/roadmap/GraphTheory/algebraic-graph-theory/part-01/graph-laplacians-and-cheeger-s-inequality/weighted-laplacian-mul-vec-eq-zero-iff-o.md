# Kernel of the weighted Laplacian of an arc network connected from a root

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$; loops $t(e) = h(e)$ and parallel or antiparallel arcs are allowed. Let $B$ be the head-positive incidence matrix, the real $V \times E$ matrix with $B_{v e} = [h(e) = v] - [t(e) = v]$, so that a loop gives a zero column. For real arc weights $w \in \mathbb{R}^E$ write $L_w = B \operatorname{diag}(w) B^{\mathsf T}$ for the weighted Laplacian. Let $G_w$ be the simple graph on $V$ in which distinct nodes $u \ne v$ are adjacent when some arc $e$ with $w_e > 0$ runs from $u$ to $v$ or from $v$ to $u$. Suppose $w_e \ge 0$ for every arc $e$, and that some node $r$ is joined to every node of $V$ by a walk in $G_w$. Then for every $x : V \to \mathbb{R}$, $L_w x = 0$ if and only if $x(v) = x(r)$ for every node $v$: the kernel of $L_w$ consists of the constant vectors.

## Sources

- C. Godsil and G. Royle, *Algebraic Graph Theory*, Graduate Texts in Mathematics 207, Springer, 2001, Chapter 13.
