# Grid product of a single-jump step function

For a finite set $P \subseteq \mathbb{R}$, let $\operatorname{prev}_P(x)$ be the largest element of $P$ below $x$ (or $x$ if there is none), and let the grid product of $A$ over $P$ be $\prod_{x \in P} \big(1 + A(x) - A(\operatorname{prev}_P(x))\big)$. Let $c \in P$ not be the minimum of $P$, and let $A(t) = y_1$ for $t \ge c$ and $A(t) = y_0$ for $t < c$. Then the grid product of $A$ over $P$ is $1 + y_1 - y_0$.
