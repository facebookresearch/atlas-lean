# Incidence graph of a trapezoidal decomposition

Let $F \subseteq \mathbb{R}^2$ have a trapezoidal decomposition: open vertical trapezoids $T_1, \dots, T_m$ (each $T$ given by reals $x_1 < x_2$ and affine lower and upper side lines $b, u$ with $b(x_1) \le u(x_1)$, $b(x_2) \le u(x_2)$, and $b(x_1) < u(x_1)$ or $b(x_2) < u(x_2)$; its carrier is $\{ (x,y) : x_1 < x < x_2,\ b(x) < y < u(x) \}$) and walls $S_1, \dots, S_k$ (open vertical segments $\{ x_S \} \times (y_1, y_2)$), such that the carriers of distinct cells are disjoint and their union is $F$. A wall $S$ is incident to a trapezoid $T$ when it lies on the right side of $T$ ($x_2 = x_S$, $b(x_2) \le y_1$, $y_2 \le u(x_2)$) or on its left side ($x_1 = x_S$, $b(x_1) \le y_1$, $y_2 \le u(x_1)$). The incidence graph is the simple graph whose vertices are the cells (trapezoid indices and wall indices) and in which a trapezoid and a wall are adjacent exactly when they are incident. Two trapezoids, or two walls, are never adjacent, so the graph is bipartite.

## Sources

S. M. LaValle, *Planning Algorithms*, Cambridge University Press, 2006, Section 6.2.2.
