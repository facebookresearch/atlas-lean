# Identity row of a time-ordered product whose active increments vanish in that row

Let $\iota$ be a finite set of states and write $I$ for the identity matrix in $\mathbb{R}^{\iota \times \iota}$. For matrices $A_0, \dots, A_{k-1} \in \mathbb{R}^{\iota \times \iota}$ and a set of active indices given by a predicate on $\{0, \dots, k-1\}$, the time-ordered product is

$$O(A) = M_0 M_1 \cdots M_{k-1}, \qquad M_j = I + A_j \text{ if } j \text{ is active}, \quad M_j = I \text{ otherwise},$$

with factors multiplied in increasing order of $j$, and $O(A) = I$ when $k = 0$.

For every $k$, all matrices $A_0, \dots, A_{k-1}$, every set of active indices and every state $h$: if $A_j(h, l) = 0$ for every active index $j$ and every state $l$, then

$$O(A)(h, l) = I(h, l) \qquad \text{for every state } l,$$

where $I(h, l)$ is $1$ for $l = h$ and $0$ otherwise.
