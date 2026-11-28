# Increment of a step cumulative hazard over an interval with no jump before its right end

Let $\iota$ be a finite set of states and write $I$ for the identity matrix in $\mathbb{R}^{\iota \times \iota}$. Let $t_0, \dots, t_{k-1}$ be real jump times and $A_0, \dots, A_{k-1} \in \mathbb{R}^{\iota \times \iota}$ jump matrices. The step cumulative hazard is

$$\Lambda(x) = \sum_{j \,:\, t_j \le x} A_j \qquad (x \in \mathbb{R}),$$

and, for reals $a$ and $b$, the time-ordered jump product over $(a, b]$ is

$$P(a, b) = \prod_{j \,:\, a < t_j \le b}^{\rightarrow} (I + A_j),$$

the product of the factors $I + A_j$ over the indices $j$ with $a < t_j \le b$, multiplied in increasing order of $j$ (the identity when there is no such index).

Assume the jump times are pairwise distinct ($t_j = t_{j'}$ only when $j = j'$). For all reals $a \le b$ such that every jump time $t_j$ with $a < t_j \le b$ equals $b$,

$$I + \big(\Lambda(b) - \Lambda(a)\big) = P(a, b).$$
