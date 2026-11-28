# Generic lower-side points lie outside the free set

A vertical trapezoid $T$ in the Euclidean plane is given by reals $x_1 < x_2$ and affine functions $b, u : \mathbb{R} \to \mathbb{R}$ (the lower and upper side lines) with $b(x_1) \le u(x_1)$, $b(x_2) \le u(x_2)$, and $b(x_1) < u(x_1)$ or $b(x_2) < u(x_2)$. Its carrier is the open set $\{ (x, y) : x_1 < x < x_2,\ b(x) < y < u(x) \}$. Its lower side is $\{ (x, y) : x_1 \le x \le x_2,\ y = b(x) \}$ and its upper side is $\{ (x, y) : x_1 \le x \le x_2,\ y = u(x) \}$. A wall is given by reals $x_S$ and $y_1 < y_2$; its carrier is the open vertical segment $\{ x_S \} \times (y_1, y_2)$. A trapezoidal decomposition of a set $F \subseteq \mathbb{R}^2$ consists of finitely many vertical trapezoids $T_1, \dots, T_m$ and walls $S_1, \dots, S_k$ such that the carriers of any two distinct cells are disjoint and the union of all carriers is $F$. Let $T_i$ be a trapezoid of the decomposition with vertical sides at $x_1 < x_2$, and let $q$ be a point of its lower side with $x_1 < q_x < x_2$ and $q_x \neq x_{S_j}$ for every wall $S_j$. Then $q \notin F$.

## Sources

S. M. LaValle, *Planning Algorithms*, Cambridge University Press, 2006, Section 6.2.2.
