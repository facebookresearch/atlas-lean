# Optimality system for linear-quadratic elliptic optimal control

Let $\Omega \subset \mathbb{R}^n$ be a bounded Lipschitz domain. Fix a desired state $y_\Omega \in L^2(\Omega)$, a coefficient $\beta \in L^\infty(\Omega)$, a regularization parameter $\lambda > 0$, and bounds $u_a \le u_b$ in $L^2(\Omega)$. For a control $u \in L^2(\Omega)$, let $y = Su \in H^1_0(\Omega)$ be the weak solution of

$$
-\Delta y = \beta u \ \text{ in } \Omega, \qquad y = 0 \ \text{ on } \partial\Omega.
$$

Consider the problem of minimizing

$$
J(u) = \tfrac12\lVert Su - y_\Omega\rVert_{L^2}^2 + \tfrac{\lambda}{2}\lVert u\rVert_{L^2}^2
$$

over the admissible set $U_{\mathrm{ad}} = \{u \in L^2(\Omega) : u_a \le u \le u_b \text{ a.e.}\}$.

**Theorem.**
1. The problem has a unique optimal control $u^*$.
2. Let $y^* = Su^*$, and let $p \in H^1_0(\Omega)$ be the *adjoint state*, the weak solution of $-\Delta p = y_\Omega - y^*$ in $\Omega$ with $p = 0$ on $\partial\Omega$. A control $u^* \in U_{\mathrm{ad}}$ is optimal if and only if

    $$
    u^*(x) = P_{[u_a(x),\,u_b(x)]}\Bigl(\tfrac{1}{\lambda}\beta(x)p(x)\Bigr) \quad \text{for almost every } x,
    $$

    where $P_{[a,b]}(s) = \min(b, \max(a, s))$.
3. Without control constraints, $u^* = \beta p/\lambda$, and $(y^*, p)$ solve the coupled elliptic system $-\Delta y^* = \beta^2 p/\lambda$, $-\Delta p = y_\Omega - y^*$, with homogeneous Dirichlet conditions.

**Proof.**
1. The solution map $S : L^2 \to L^2$ is linear and bounded. So $J$ is continuous and $\lambda$-strongly convex. The set $U_{\mathrm{ad}}$ is nonempty, closed and convex, so $J$ has a unique minimizer over it.
2. Since $J$ is convex, $u^*$ is optimal if and only if $\langle S^*(Su^* - y_\Omega) + \lambda u^*,\ u - u^* \rangle \ge 0$ for all $u \in U_{\mathrm{ad}}$. Testing the state and adjoint equations against each other shows $S^* z = \beta q$, where $-\Delta q = z$ with $q = 0$ on the boundary. Hence $S^*(Su^* - y_\Omega) = -\beta p$, and the variational inequality becomes $\int (\lambda u^* - \beta p)(u - u^*) \ge 0$. This holds if and only if, pointwise almost everywhere, $u^*(x)$ minimizes $\tfrac{\lambda}{2}v^2 - \beta(x)p(x)v$ over $[u_a(x), u_b(x)]$, which is the projection formula.
3. Take $u_a = -\infty$ and $u_b = +\infty$ in part 2.

## Depends on

- [Existence and uniqueness of weak solutions of the abstract Poisson problem](weak-solutions-of-elliptic-equations/exists-unique-weak-solution.md)

## Background

- [Existence and uniqueness of the Tikhonov minimizer](../convex-analysis-and-variations/tikhonov-regularization/exists-unique-tikhonov-minimizer.md)
- [Sufficiency of the KKT conditions for convex problems](../convex-analysis-and-variations/lagrange-duality/kkt-sufficient.md)

## Sources

- S. Volkwein, *Optimal Control of Elliptic Partial Differential Equations*, lecture notes, University of Konstanz, <https://www.math.uni-konstanz.de/numerik/personen/volkwein/teaching/Optimal-Control-EPDEs.pdf>:
    - Theorems 2.10, 2.12, 2.14 and 2.15: existence and uniqueness of the optimal control for $\lambda > 0$ and a nonempty closed convex admissible set;
    - Lemmas 3.13–3.14: the adjoint $S^*z = \beta p$; Definition 3.16: the adjoint state; Theorem 3.17: the variational inequality (3.10);
    - Theorems 3.19–3.20: the projection formula as a necessary and sufficient condition, with the unconstrained optimality system (3.18);
    - Theorem 3.21: the multiplier form.
