# The weighted Laplacian of an arc network is symmetric

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$; loops $t(e) = h(e)$ and parallel or antiparallel arcs are allowed. Let $B$ be the head-positive incidence matrix, the real $V \times E$ matrix with $B_{v e} = [h(e) = v] - [t(e) = v]$, so that a loop gives a zero column. For all real arc weights $w$, of any sign, the matrix $L_w = B \operatorname{diag}(w) B^{\mathsf T}$ is symmetric: $L_w^{\mathsf T} = L_w$ (over $\mathbb{R}$, Hermitian and symmetric agree).
