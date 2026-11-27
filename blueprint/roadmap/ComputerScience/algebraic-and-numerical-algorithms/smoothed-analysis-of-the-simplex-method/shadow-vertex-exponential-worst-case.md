# Exponential worst case of shadow vertex rules with fixed start and objective

For a polytope $P$, a vertex $u$ and objectives $w, c$ such that $w$ is uniquely maximized at $u$ and $c$ is uniquely maximized at a vertex $v$, the *shadow path* for $w$ from $u$ to $v$ consists of the vertices of $P$ that maximize $(1 - \lambda) w + \lambda c$ for some $\lambda \in [0, 1]$, that is, the vertices whose normal cones meet the segment $[w, c]$. Its length depends on all three choices: if $w$ and $c$ lie in the interior of the same normal cone, the path has no pivot.

- (Goldfarb) For every $d \ge 2$ there are a $d$-dimensional combinatorial cube $P$ defined by $2d$ linear inequalities (Goldfarb's deformed cube), a vertex $u$ of $P$ and objectives $w, c$ as above such that the shadow path for $w$ from $u$ to the $c$-maximizer passes through all $2^d$ vertices of $P$; so the shadow vertex rule started at $u$ with auxiliary objective $w$ makes $2^d - 1$ pivots.
- (Black, Theorem 1.1) For every $n \ge 1$ there are an $n$-dimensional simple polytope $P$ with $3n$ facets, a vertex $v$ of $P$ and an objective $c$ such that, for every auxiliary objective $w$ uniquely maximized at $v$, the shadow path for $w$ from $v$ to the $c$-maximizer has length at least $2^n$. Thus, once the start vertex and the objective are fixed, no choice of the second objective spanning the shadow plane makes the shadow vertex rule polynomial on these instances.
- (Black, Theorem 1.3) For every norm $\eta$ on $\mathbb{R}^n$ and every $n \ge 1$ there are an $n$-dimensional combinatorial cube $C_n$ and an objective $c$ such that the $\eta$-steepest-edge rule, which moves from $v^i$ to a $c$-improving neighbour $u$ maximizing $c^\top(u - v^i)/\eta(u - v^i)$, follows a path through all $2^n$ vertices of $C_n$ to maximize $c$. The norm is fixed before the instance is constructed.

Hence the polynomial smoothed bounds for shadow vertex methods do not come from worst-case behaviour.

## Proof sketch

Goldfarb's cube is obtained by repeatedly deforming a product with an interval, each of its $2d$ inequalities involving at most three consecutive variables; an induction on $d$ shows that its projection onto the plane of its last two coordinates is a polygon whose boundary passes through the images of all $2^d$ vertices, and $w, c$ are chosen in that plane so that the path follows this boundary. For Theorem 1.1, Black starts from such an exponentially long shadow path from $u$ to $v$ and adds inequalities that subdivide the normal cones of $u$ and $v$, producing vertices $a, b$ whose normal cones are arbitrarily thin and contain $w$ and $c$; every segment from the cone of $a$ to the cone of $b$ then meets every normal cone met by $[w, c]$. For Theorem 1.3, a linear map that fixes $w$ and shrinks its orthogonal complement makes all edges nearly parallel to $w$, so that for the fixed norm the steepest-edge choice coincides with the shadow rule's choice on the transformed Goldfarb cube.

## Depends on

- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Sources

- D. Goldfarb, "On the complexity of the simplex method", in Advances in Optimization and Numerical Analysis, Kluwer (1994); the construction first appeared in D. Goldfarb, "Worst case complexity of the shadow vertex simplex algorithm", technical report, Columbia University (1983).
- A. E. Black, "Exponential Lower Bounds for Many Pivot Rules for the Simplex Method", Mathematical Programming (2026), arXiv:2403.04886, Theorems 1.1 and 1.3 and Sections 3–4.
