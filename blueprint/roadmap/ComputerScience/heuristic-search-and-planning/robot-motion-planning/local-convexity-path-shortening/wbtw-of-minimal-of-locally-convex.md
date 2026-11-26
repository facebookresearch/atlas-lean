# Length-minimal polylines are straight at locally convex bends

A polyline is a finite list of points $(p_1, \dots, p_n)$ of the Euclidean plane $\mathbb{R}^2$. Its length is $\sum_{i=1}^{n-1} \|p_i - p_{i+1}\|$ (zero for the empty and one-point polylines). For $F \subseteq \mathbb{R}^2$, the polyline is feasible in $F$ when every closed segment $[p_i, p_{i+1}]$ lies in $F$ and, for a one-point polyline, $p_1 \in F$; the empty polyline is feasible. Write $L_1 \mathbin{+\!\!+} L_2$ for concatenation.

Let $F \subseteq \mathbb{R}^2$, let $l_1, l_2$ be polylines and $a, b, c \in \mathbb{R}^2$, and put $L = l_1 \mathbin{+\!\!+} (a, b, c) \mathbin{+\!\!+} l_2$. Assume

- $L$ is feasible in $F$;
- some neighborhood $U$ of $b$ has $U \cap F$ convex;
- $L$ is length-minimal: every polyline $L'$ feasible in $F$ with the same first vertex and the same last vertex as $L$ has length at least that of $L$.

Then $b$ lies on the closed segment $[a, c]$.
