# Exact subset sum procedure

Given a list $x$ of natural numbers and a target
$t \in \mathbb{N}$, the procedure first computes the list $L = (\ell_1, \dots, \ell_m)$ of
attainable sums of $x$ with target $t$, then scans it from left to right, keeping a running
maximum that starts at $0$, and returns $\max(0, \ell_1, \dots, \ell_m)$. Its counted events
are those of computing $L$ plus one per entry of $L$.
