# Slow all-pairs shortest paths (SLOW-APSP)

Let $W$ and $L^{(0)}$ be $n \times n$ matrices
over the min-plus semiring on $\mathbb{Z} \cup \{\infty\}$, in which addition is $\min$ and
multiplication is $+$. SLOW-APSP copies $L^{(0)}$ cell by cell and then runs $\max(n - 1, 0)$
phases. Phase $r$ fills a fresh $n \times n$ matrix $M$ with $\infty$, then for each triple
$(i, j, k)$ in increasing $i$-$j$-$k$ order sets $M_{ij} \leftarrow \min(M_{ij}, L^{(r-1)}_{ik} +
W_{kj})$, and finally copies $M$ cell by cell to give $L^{(r)}$; the result is $L^{(n-1)}$. The
cost is a triple of natural numbers: the first coordinate counts one assignment for each cell
copied or filled, and the second and third coordinates count one scalar addition and one scalar
minimum for each update $M_{ij} \leftarrow \min(M_{ij}, L^{(r-1)}_{ik} + W_{kj})$.

Accumulator updates inside the loop are not charged as assignments.
