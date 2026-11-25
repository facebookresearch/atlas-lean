# Forward error bounded by condition times backward error

Let $f : D \to R$ and $\hat f$ be as on the error-notions page, let $x \in D$ and $\eta \ge 0$, and suppose there is a witness
$\Delta x$ with $\lVert \Delta x \rVert \le \eta$, $x + \Delta x \in D$ and $\hat f(x) = f(x + \Delta x)$ (a backward error at most $\eta$ in the
infimum sense does not by itself provide one). If $\lVert f(x + d) - f(x) \rVert \le \kappa \lVert d \rVert$ for every $d$ with
$\lVert d \rVert \le \eta$ and $x + d \in D$, then $\lVert \hat f(x) - f(x) \rVert \le \kappa\eta$. Relatively, if $x \ne 0$, $f(x) \ne 0$,
$\lVert \Delta x \rVert \le \eta \lVert x \rVert$ and $\lVert f(x + d) - f(x) \rVert / \lVert f(x) \rVert \le \kappa_{\mathrm{rel}} \lVert d \rVert / \lVert x \rVert$ for every $d$
with $\lVert d \rVert \le \eta \lVert x \rVert$ and $x + d \in D$, then the relative forward error is at most $\kappa_{\mathrm{rel}}\eta$. This is an exact inequality; first-order versions need differentiability and are separate.

## Proof

Take $d = \Delta x$ in the hypothesis.

## Depends on

- [Forward error, backward error and conditioning interface](forward-error-backward-error-and-conditioning-interface.md)

## Related topics

- [Distance to the nearest singular operator](../../../LinearAlgebra/matrix-decompositions/perturbation-theory-for-linear-systems/condition-number-bound/is-least-norm-of-not-is-unit-sub.md)
- [Small perturbations of an invertible element stay invertible](../../../LinearAlgebra/matrix-decompositions/perturbation-theory-for-linear-systems/condition-number-bound/is-unit-sub.md)

## Sources

- CS 4220 lecture notes: review / introduction (Spring 2023) — D. Bindel, Cornell University CS 4220. <https://www.cs.cornell.edu/courses/cs4220/2023sp/lec/review.pdf> Sec. 1 (forward error related to backward error through a condition number) and Sec. 3.6.
