# Scanning a list of edges

Starting from a Kruskal scan state $s$, scanning a list of
validated edges $e_1, \dots, e_k$ applies one Kruskal step to each edge in list order: the scan
of the empty list returns $s$, and the scan of $e_1, \dots, e_k$ is the scan of $e_2, \dots, e_k$
from the state obtained by processing $e_1$ in $s$.
