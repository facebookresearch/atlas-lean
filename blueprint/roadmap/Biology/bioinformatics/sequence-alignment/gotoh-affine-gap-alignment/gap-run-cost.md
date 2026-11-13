# Cost of a gap run

Given an integer gap-open cost $o$, an integer gap-extend cost $e$, gap
states $p$ (of the column before the run) and $c$ (of the run's columns) and a length
$k \in \mathbb{N}$, the cost of a run of $k$ gap columns is $k e$ if $p = c$ (the run continues
an open run); otherwise it is $0$ for $k = 0$ and $o + (k - 1) e$ for $k \ge 1$.
