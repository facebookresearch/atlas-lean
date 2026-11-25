# Fenchel duality in finite dimensions

Let $f : \mathbb{R}^n \to (-\infty, \infty]$ and $g : \mathbb{R}^m \to (-\infty, \infty]$ be convex functions, neither identically $+\infty$, let $A$ be a real $m \times n$ matrix, and let $f^*$ and $g^*$ be their convex conjugates. For all $x \in \mathbb{R}^n$ and $z \in \mathbb{R}^m$, $-g^*(z) - f^*(-A^{\mathsf T}z) \le f(x) + g(Ax)$ (weak duality): adding Fenchel's inequalities $f(x) + f^*(-A^{\mathsf T}z) \ge -z^{\mathsf T}Ax$ and $g(Ax) + g^*(z) \ge z^{\mathsf T}Ax$ gives it, and both conjugates are greater than $-\infty$ because $f$ and $g$ are not identically $+\infty$. If some $\hat x$ lies in the interior of $\operatorname{dom} f$ with $A\hat x$ in the interior of $\operatorname{dom} g$, then $\inf_x (f(x) + g(Ax)) = \sup_z (-g^*(z) - f^*(-A^{\mathsf T}z))$, and when this common value is finite the supremum is attained. The dual is the Lagrange dual of minimizing $f(x) + g(y)$ subject to $Ax = y$, and the interior-point condition implies Slater's condition for that problem. The same equality and dual attainment hold under the weaker condition that some $\hat x \in \operatorname{dom} f$ has $A\hat x \in \operatorname{dom} g$ with $g$ finite and continuous at $A\hat x$; for example $f$ the indicator of $\{0\}$ and $g = 0$ satisfy it although $\operatorname{dom} f$ has empty interior. That version, and infinite-dimensional ones, are separate statements.

## Proof depends on

- [Strong duality under Slater's condition with affine equality constraints](../lagrange-duality/strong-duality-under-slater-with-affine-equality-constraints.md): strong duality and dual attainment for the reformulated problem with the equality constraint $Ax = y$.

## Sources

- L. Vandenberghe, *ECE236C Optimization methods for large-scale systems*, lecture "Conjugate functions", UCLA, <https://www.seas.ucla.edu/~vandenbe/236C/lectures/conj.pdf>, slide "Duality" (5.21)
- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, §3.3.2 (Fenchel's inequality)
