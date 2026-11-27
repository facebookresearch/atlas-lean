# Time-ordered products of matrices with no return to the transient state

Let $r$ and $k$ be natural numbers and let the state space be $\{\star\} \sqcup \{0, \dots, r-1\}$, with $\star$ the transient state. Matrices on these states have real entries, and $I$ is the identity matrix. A matrix $M$ on these states has no return if $M(c, \star) = 0$ for every cause $c$.

For matrices $A_0, \dots, A_{k-1}$ on these states and a set of active indices, the time-ordered product is $O(A) = M_0 M_1 \cdots M_{k-1}$, with $M_j = I + A_j$ if $j$ is active and $M_j = I$ otherwise (the identity when $k = 0$).

For every $k$, all matrices $A_0, \dots, A_{k-1}$ and every set of active indices: if every $A_j$ has no return, then

1. $O(A)$ has no return, and
2. its transient-to-transient entry is

    $$
    O(A)(\star, \star) = \prod_{j=0}^{k-1} \begin{cases} 1 + A_j(\star, \star) & \text{if } j \text{ is active}, \\ 1 & \text{otherwise.} \end{cases}
    $$
