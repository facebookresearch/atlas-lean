# Chain product of a step cumulative hazard over a sorted list containing the jump times

Let $\iota$ be a finite set of states and write $I$ for the identity matrix in $\mathbb{R}^{\iota \times \iota}$. Let $t_0, \dots, t_{k-1}$ be real jump times and $A_0, \dots, A_{k-1} \in \mathbb{R}^{\iota \times \iota}$ jump matrices. The step cumulative hazard is

$$\Lambda(x) = \sum_{j \,:\, t_j \le x} A_j \qquad (x \in \mathbb{R}),$$

and, for reals $a$ and $b$, the time-ordered jump product over $(a, b]$ is

$$P(a, b) = \prod_{j \,:\, a < t_j \le b}^{\rightarrow} (I + A_j),$$

the product of the factors $I + A_j$ over the indices $j$ with $a < t_j \le b$, multiplied in increasing order of $j$ (the identity when there is no such index).

For a matrix-valued function $\Lambda$ and a list of reals $(x_0, x_1, \dots, x_p)$, the chain product is

$$\Pi_\Lambda(x_0, \dots, x_p) = \big(I + \Lambda(x_1) - \Lambda(x_0)\big) \big(I + \Lambda(x_2) - \Lambda(x_1)\big) \cdots \big(I + \Lambda(x_p) - \Lambda(x_{p-1})\big),$$

multiplied left to right, with $\Pi_\Lambda(x_0) = I$.

Assume the jump times are strictly increasing, $t_0 < t_1 < \dots < t_{k-1}$. For every list of reals $(x_0, x_1, \dots, x_p)$ with $p \ge 0$ and every real $z$, if

- $x_0 < x_1 < \dots < x_p$,
- $z$ is one of $x_0, \dots, x_p$,
- $x_i \le z$ for every $i$, and
- every jump time $t_j$ with $x_0 < t_j \le z$ is one of $x_0, \dots, x_p$,

then

$$\Pi_\Lambda(x_0, x_1, \dots, x_p) = P(x_0, z).$$
