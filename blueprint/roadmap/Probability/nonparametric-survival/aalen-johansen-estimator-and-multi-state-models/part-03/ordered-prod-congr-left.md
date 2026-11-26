# Time-ordered products depend only on the active factors

Let $\iota$ be a finite set of states and write $I$ for the identity matrix in $\mathbb{R}^{\iota \times \iota}$. For matrices $A_0, \dots, A_{k-1} \in \mathbb{R}^{\iota \times \iota}$ and a set of active indices given by a predicate on $\{0, \dots, k-1\}$, the time-ordered product is

$$O(A) = M_0 M_1 \cdots M_{k-1}, \qquad M_j = I + A_j \text{ if } j \text{ is active}, \quad M_j = I \text{ otherwise},$$

with factors multiplied in increasing order of $j$, and $O(A) = I$ when $k = 0$.

For all families $A_0, \dots, A_{k-1}$ and $A'_0, \dots, A'_{k-1}$ of matrices and every set of active indices: if $A_j = A'_j$ for every active index $j$, then

$$O(A) = O(A'),$$

both products being taken with the same active indices.
