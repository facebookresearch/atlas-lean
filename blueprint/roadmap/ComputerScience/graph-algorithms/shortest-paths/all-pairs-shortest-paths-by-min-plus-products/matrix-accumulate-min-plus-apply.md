# Entries of the min-plus matrix accumulator

Let $A$, $B$ and $C$ be $n \times n$
matrices with entries in $\mathbb{Z} \cup \{\infty\}$, viewed in the min-plus semiring. For all
$i, j \in \{0, \dots, n-1\}$, the entry $(i, j)$ of the matrix returned by the matrix
accumulator on $A$, $B$ and the accumulator $C$ equals
$\min\bigl(C_{ij}, \min_{k} (A_{ik} + B_{kj})\bigr)$, where $k$ ranges over
$\{0, \dots, n-1\}$.
