# Pick's theorem for convex lattice polygons

Let $V \subset \mathbb{Z}^2$ be a finite
set of lattice points, let $P \subset \mathbb{R}^2$ be the convex hull of $V$, and suppose that
$P$ has nonempty interior. Let $I$ be the number of points of $\mathbb{Z}^2$ in the interior of
$P$ and $B$ the number of points of $\mathbb{Z}^2$ on the boundary of $P$. Then the area
(two-dimensional Lebesgue measure) of $P$ equals $I + B/2 - 1$.

Proof: The triangle case counts lattice points in a half-open fundamental
parallelogram. A crossing diagonal then cuts larger polygons into two smaller
full-dimensional lattice polygons, allowing strong induction on the vertex set.

## Sources

- Eugen J. Ionascu, "A Parametrization of Equilateral Triangles Having Integer Coordinates", Journal of Integer Sequences 10 (2007), Article 07.6.7, standard formula `Area = #b / 2 + #i - 1`, lines 87–100, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Ionascu/ionascu2.tex>; Kevin A. Broughan, "The gcd-sum function", Journal of Integer Sequences 4 (2001), Article 01.2.2, trapezium application, lines 699–715 (the prose there prints "+1" but the paper's own derived formula, equation label `10`, uses the minus-one form), <https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex>; Gil Alon and Pete L. Clark, "On the Number of Representations of an Integer by a Linear Form", Journal of Integer Sequences 8 (2005), Article 05.5.2, generalized lattice version `A(P) = δ * (h + b / 2 - 1)`, lines 633–638 (this module is the `δ = 1` standard-lattice case), <https://cs.uwaterloo.ca/journals/JIS/VOL8/Clark/clark80.tex>.
