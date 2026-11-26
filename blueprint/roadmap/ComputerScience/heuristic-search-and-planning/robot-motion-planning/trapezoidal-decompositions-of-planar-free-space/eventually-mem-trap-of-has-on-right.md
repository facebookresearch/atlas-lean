# Points just left of a wall lie in the trapezoid on its left

A vertical trapezoid $T$ in the Euclidean plane is given by reals $x_1 < x_2$ and affine functions $b, u : \mathbb{R} \to \mathbb{R}$ (the lower and upper side lines) with $b(x_1) \le u(x_1)$, $b(x_2) \le u(x_2)$, and $b(x_1) < u(x_1)$ or $b(x_2) < u(x_2)$. Its carrier is the open set $\{ (x, y) : x_1 < x < x_2,\ b(x) < y < u(x) \}$. A wall is given by reals $x_S$ and $y_1 < y_2$; its carrier is the open vertical segment $\{ x_S \} \times (y_1, y_2)$. A trapezoidal decomposition of a set $F \subseteq \mathbb{R}^2$ consists of finitely many vertical trapezoids $T_1, \dots, T_m$ and walls $S_1, \dots, S_k$ such that the carriers of any two distinct cells are disjoint and the union of all carriers is $F$. A wall $S$ lies on the right side of $T$ when $x_2 = x_S$, $b(x_2) \le y_1$ and $y_2 \le u(x_2)$; it lies on the left side of $T$ when $x_1 = x_S$, $b(x_1) \le y_1$ and $y_2 \le u(x_1)$. Let the wall $S_j = \{ x_{S_j} \} \times (y_1, y_2)$ lie on the right side of the trapezoid $T_i$, and let $q$ be a point of the carrier of $S_j$. Then for every sufficiently small $t > 0$, the point $(x_{S_j} - t, q_y)$ lies in the carrier of $T_i$.

## Sources

S. M. LaValle, *Planning Algorithms*, Cambridge University Press, 2006, Section 6.2.2.
