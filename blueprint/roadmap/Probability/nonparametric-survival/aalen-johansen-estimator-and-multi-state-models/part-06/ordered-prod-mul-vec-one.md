# Time-ordered products of identity plus zero-row-sum matrices have unit row sums

Let $\iota$ be a finite set of states and write $I$ for the identity matrix in $\mathbb{R}^{\iota \times \iota}$. For matrices $A_0, \dots, A_{k-1} \in \mathbb{R}^{\iota \times \iota}$ and a set of active indices given by a predicate on $\{0, \dots, k-1\}$, the time-ordered product is

$$O(A) = M_0 M_1 \cdots M_{k-1}, \qquad M_j = I + A_j \text{ if } j \text{ is active}, \quad M_j = I \text{ otherwise},$$

with factors multiplied in increasing order of $j$, and $O(A) = I$ when $k = 0$.

Write $\mathbf{1} \in \mathbb{R}^{\iota}$ for the all-ones vector. For every $k$, all matrices $A_0, \dots, A_{k-1}$ and every set of active indices: if $A_j \mathbf{1} = 0$ for every $j \in \{0, \dots, k-1\}$ (every row of every $A_j$ sums to $0$), then

$$O(A)\, \mathbf{1} = \mathbf{1},$$

that is, every row of $O(A)$ sums to $1$.
