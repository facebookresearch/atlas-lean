# Observability in a linear flowsheet model

Write the balances and meter readings of a flowsheet as $Mx = d$, with $M = \begin{pmatrix} A \\ H \end{pmatrix}$ a real linear map
on a finite-dimensional space of flows, $A$ the balances and $H$ the meters, and let $x_0$ be a solution. The solution set is
$x_0 + \ker M$, and a linear functional $\ell$ of the flows is constant on it, so determined by the data, if and only if
$\ell(v) = 0$ for every $v \in \ker M$; then $\ell(x) = \ell(x_0)$ for all solutions.

For example, with streams (fresh feed $f$, flow to the second unit $u$, recycle $r$, product $p$), balances $f + r - u = 0$ and
$u - r - p = 0$, and meters on $f$ and $p$, the kernel is spanned by $(0, 1, 1, 0)$: the recycle flow is not observable, and a
positive flow stays positive under small perturbations along this direction. Adding a meter on $r$ makes every flow observable. The
equivalence is stated on the whole affine solution set; on the boundary of a set of nonnegative flows it is not claimed.

## Depends on

## Proof depends on

## Sources

- J. Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, edition 6 (version 6.11), Appendix A.4.2, the kernel of a matrix, <https://www.jirka.org/diffyqs/>.
