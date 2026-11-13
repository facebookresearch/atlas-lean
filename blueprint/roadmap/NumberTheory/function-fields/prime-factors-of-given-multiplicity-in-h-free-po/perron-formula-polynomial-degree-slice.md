# Perron's formula for degree slices of monic polynomials

Let $F$ be a finite field,
let $M_m$ be the set of monic polynomials of degree $m$ over $F$, let
$a \colon F[X] \to \mathbb{C}$, and write $c_m = \sum_{f \in M_m} a(f)$. Let $r$ be a real
number with $0 < r < 1$ such that the series $\sum_{m \ge 0} |c_m| r^m$ converges, and let
$A \colon \mathbb{C} \to \mathbb{C}$ satisfy $A(u) = \sum_{m \ge 0} c_m u^m$ for every
complex $u$ with $|u| = r$. Then for every $n \ge 0$,

$$c_n = \frac{1}{2\pi i} \oint_{|u| = r} \frac{A(u)}{u^{n+1}}\, du,$$

where the circle $|u| = r$ is traversed once counterclockwise.

Convergence of $\sum |c_m| r^m$ at the single radius $r$ stands in for the paper's uniform
absolute convergence on the closed disk, and $A$ only has to agree with the series on the
circle, the only values the contour integral sees.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 9.
