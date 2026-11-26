# Traceback through a weighted interval scheduling table

For weights $w$ and arrays
$M$ and $P$, the traceback from $0$ returns $\emptyset$; from $j \ge 1$, with
$q = \min(P_j, j - 1)$, it charges one unit for comparing $M_{j-1} < w(j) + M_q$ and returns
$\{j\}$ together with the traceback from $q$ if this holds, and the traceback from $j - 1$
otherwise.
