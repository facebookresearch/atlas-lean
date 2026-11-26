# Exponential worst case of shadow vertex rules for every choice of projection

For every $d \ge 2$ there is a $d$-dimensional polytope defined by $2d$ linear inequalities (Goldfarb's deformed cube) and a $2$-dimensional plane onto which all $2^d$ vertices project to vertices of the shadow, so the shadow vertex rule for that plane makes $2^d - 1$ pivots. Moreover there are linear programs on which every choice of projection plane for shadow rule variants leads to exponentially many pivots, and steepest-edge rule variants are exponential for every choice of norm. Hence the polynomial smoothed bounds for shadow vertex methods do not come from worst-case behaviour.

## Proof sketch

Goldfarb's cube is a combinatorial cube obtained by repeatedly deforming a product with an interval, each of its $2d$ inequalities involving at most three variables; an induction on $d$ shows that its projection onto a suitable fixed plane is a polygon whose boundary passes through the images of all $2^d$ vertices. Black's constructions combine products and deformations so that, for every projection plane, a large part of the vertex set survives on the shadow path, and analogous constructions defeat every norm used to normalize steepest-edge directions.

## Depends on

- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Sources

- D. Goldfarb, "On the complexity of the simplex method", in Advances in Optimization and Numerical Analysis, Kluwer (1994).
- A. E. Black, "Exponential Lower Bounds for Many Pivot Rules for the Simplex Method", Mathematical Programming (2026), arXiv:2403.04886.
