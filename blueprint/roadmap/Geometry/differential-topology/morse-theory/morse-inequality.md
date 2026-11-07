# Morse inequalities

Let $M$ be a compact Hausdorff smooth manifold without boundary,
modelled on a finite-dimensional real normed space, and let $f : M \to \mathbb{R}$ be a Morse
function: $f$ is $C^\infty$, has finitely many critical points, and the Hessian of $f$ at each
critical point, computed in the preferred chart, is a nondegenerate bilinear form. The Morse index
of a critical point is the largest dimension of a subspace on which this Hessian is negative
definite. For $j \in \mathbb{N}$ let $c_j$ be the number of critical points of $f$ of Morse index
$j$, and let $b_j$ be the dimension of the singular homology $H_j(M; \mathbb{R})$ (taken to be $0$
if infinite). Then for every $k \in \mathbb{N}$,

$$\sum_{j=0}^{k} (-1)^{k-j} b_j \le \sum_{j=0}^{k} (-1)^{k-j} c_j.$$

## Sources

- M. Morse, The Calculus of Variations in the Large, AMS Colloq. Publ. 18 (1934). Listed as §40 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `morse_inequality`.
