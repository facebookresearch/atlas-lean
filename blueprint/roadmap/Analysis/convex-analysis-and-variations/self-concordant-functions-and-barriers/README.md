# Self-concordant functions and barriers

Self-concordance (Nesterov and Nemirovski) explains why Newton's method and interior-point methods run in polynomial time. A convex function is [self-concordant](is-self-concordant.md) when its third derivative is bounded by the $3/2$ power of its second derivative, $|D^3F(x)[h,h,h]| \le 2(D^2F(x)[h,h])^{3/2}$, so that its Hessian is Lipschitz in the local norm $|h|_x$ that the Hessian defines; every statement is then affine-invariant, like Newton's method itself. Within the unit Dikin ellipsoid $\{y : |y - x|_x < 1\}$ the function stays [defined](mem-of-dikin-lt-one.md) and is [bounded](bounds-of-dikin-lt-one.md) by explicit logarithmic models. A [$\vartheta$-self-concordant barrier](is-self-concordant-barrier.md) also has its gradient bounded in the local norm by $\sqrt{\vartheta}$; the barrier is [semibounded](deriv-le-of-is-self-concordant-barrier.md), $DF(x)[y - x] \le \vartheta$, and path-following methods reach accuracy $\epsilon$ in $O(\sqrt{\vartheta} \log(1/\epsilon))$ Newton steps. The basic example is [$-\log$](is-self-concordant-barrier-neg-log.md), a $1$-barrier for the ray; sums give the $m$-barrier $-\sum \log(b_i - a_i^T x)$ of a polyhedron with $m$ constraints.

Directional derivatives are written as derivatives of the restrictions $t \mapsto F(x + th)$ to lines.

- [Self-concordant function](is-self-concordant.md)
- [Self-concordant barrier](is-self-concordant-barrier.md)
- [$-\log$ is a $1$-self-concordant barrier for the nonnegative ray](is-self-concordant-barrier-neg-log.md)
- [The open unit Dikin ellipsoid lies in the domain](mem-of-dikin-lt-one.md)
- [Bounds on a self-concordant function in the Dikin ellipsoid](bounds-of-dikin-lt-one.md)
- [Semiboundedness of a self-concordant barrier](deriv-le-of-is-self-concordant-barrier.md)

## Related topics

- [Newton's method for minimization](../newton-s-method-for-minimization/README.md): the quadratic convergence phase under a Lipschitz Hessian in a fixed norm, which self-concordance makes affine-invariant.
- [Lagrange duality](../lagrange-duality/README.md): the duality gap $m/t$ of the logarithmic barrier method.
- [Trust-region methods](../../numerical-analysis/trust-region-methods/README.md): the unit Dikin ellipsoid $\{y : |y - x|_x < 1\}$ is a region shaped by the local norm in which a self-concordant function stays defined and is bounded by explicit models around $x$, the role a trust region plays for the quadratic model.
