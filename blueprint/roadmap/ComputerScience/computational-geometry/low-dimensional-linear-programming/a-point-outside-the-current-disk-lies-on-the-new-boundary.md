# A point outside the current disk lies on the new boundary

For finite sets $Q, R \subseteq \mathbb{R}^2$ with $|R| \le 2$, let $D(Q, R)$ be a closed disk of smallest radius that contains $Q \cup R$ and has every point of $R$ on its boundary circle, when such a disk exists.
1. If $Q \cup R \neq \emptyset$ and $D(Q, R)$ exists, it is unique (for $Q = R = \emptyset$ every disk of radius $0$ qualifies): two such disks of the same radius $r$ with distinct centres at distance $\rho$ would give a smaller one, centred at the midpoint of the centres with radius $\sqrt{r^2 - \rho^2/4}$, which contains their intersection and has every common boundary point on its boundary.
2. Let $p_1, \dots, p_i$ be points of $\mathbb{R}^2$ and $R$ a set of at most one point with $i \ge 2$, and suppose $D(\{p_1, \dots, p_i\}, R)$ exists. If $p_i \notin D(\{p_1, \dots, p_{i-1}\}, R)$, then $p_i$ lies on the boundary circle of $D(\{p_1, \dots, p_i\}, R)$, that is, $D(\{p_1, \dots, p_i\}, R) = D(\{p_1, \dots, p_{i-1}\}, R \cup \{p_i\})$. For $R = \emptyset$ this says that if $p_i \notin B_{i-1}$ then $p_i$ lies on the boundary of $B_i$, where $B_i$ is the minimum enclosing disk of $p_1, \dots, p_i$.

No general-position assumption is needed.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 21, the claim that if $p_i \notin B_{i-1}$ then $p_i$ is on the boundary of $B_i$
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Smallest enclosing circles and more", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides4b.pdf>: slides 15 and 23, the insertion step for the smallest enclosing circle of $p_1, \dots, p_i$ and for the smallest enclosing circle with a given point $p$ on its boundary (if the new point is outside the current circle, it lies on the boundary of the new one)
