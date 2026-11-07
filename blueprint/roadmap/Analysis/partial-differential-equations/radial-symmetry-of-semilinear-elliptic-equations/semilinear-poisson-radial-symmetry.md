# Radial symmetry of positive solutions of the semilinear Poisson problem

Let $n \ge 1$,
let $f : \mathbb{R} \to \mathbb{R}$ be Lipschitz, and let $u : \mathbb{R}^n \to \mathbb{R}$ be a
function on Euclidean space that is $C^2$ on the closed unit ball $\overline{B}$. Suppose that $u$
solves the semilinear Poisson problem for $f$, that is, $-\Delta u = f(u)$ on the open unit ball
$B$ and $u = 0$ on the unit sphere, and that $u > 0$ on $B$. Then there is a function
$v : \mathbb{R} \to [0, \infty)$ that is strictly decreasing on $[0, 1]$ and satisfies
$u(x) = v(\|x\|)$ for every $x \in \overline{B}$.

## Sources

- B. Gidas, W. M. Ni, and L. Nirenberg, Symmetry and related properties via the maximum principle, Comm. Math. Phys. 68 (1979), 209-243. Also stated as Theorem 2 (Radial symmetry) in L. C. Evans, Partial Differential Equations, Section 9 on nonvariational techniques. Via leanprover/lean-eval@38361be, problem `semilinear_poisson_radial_symmetry`.
