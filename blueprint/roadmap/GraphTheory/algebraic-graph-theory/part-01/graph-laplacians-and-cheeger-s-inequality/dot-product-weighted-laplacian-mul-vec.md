# Energy identity for the weighted Laplacian of an arc network

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$; loops $t(e) = h(e)$ and parallel or antiparallel arcs are allowed. Let $B$ be the head-positive incidence matrix, the real $V \times E$ matrix with $B_{v e} = [h(e) = v] - [t(e) = v]$, so that a loop gives a zero column. For real arc weights $w \in \mathbb{R}^E$ write $L_w = B \operatorname{diag}(w) B^{\mathsf T}$ for the weighted Laplacian. For all real weights $w$, of any sign, and every $x : V \to \mathbb{R}$,

$$x^{\mathsf T} L_w x = \sum_{e \in E} w_e \big(x(h(e)) - x(t(e))\big)^2.$$

Loops contribute $0$ to the sum. Replacing $B$ by the tail-positive matrix $-B$ leaves $L_w$ unchanged.

## Sources

- C. Godsil and G. Royle, *Algebraic Graph Theory*, Graduate Texts in Mathematics 207, Springer, 2001, Chapter 13.
