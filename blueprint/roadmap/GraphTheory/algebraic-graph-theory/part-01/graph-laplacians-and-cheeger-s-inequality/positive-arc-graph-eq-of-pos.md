# With positive weights, the graph of positive arcs is the underlying graph

Let $V$ and $E$ be sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its head
$h(e)$, and for weights $w \in \mathbb{R}^E$ let $G_w$ be the simple graph on $V$ in which
$u \neq v$ are adjacent when some arc $e$ with $w_e > 0$ joins them in either direction. If
$r_e > 0$ for every arc $e$, then $G_r = G_1$, the graph for the constant weight $1$: every arc
counts, with its orientation ignored and loops dropped.
