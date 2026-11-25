# For q ≠ 0 the fixed-free displacement is not a fixed-fixed solution

Let $L > 0$, $EA > 0$ and $q \ne 0$, and let $u(x) = q\, x\, (2L - x)/(2\, EA)$ be the
[fixed-free displacement](fixed-free-displacement.md). Then, with ordinary derivatives on
$\mathbb{R}$,

- $-EA\, u''(x) = q$ for every real $x$;
- $u(0) = 0$ (fixed end);
- $EA\, u'(L) = 0$ (traction-free end);

but $u$ does not solve the [fixed-fixed problem](is-fixed-fixed-solution.md) on $[0, L]$ with
rigidity $EA$ and constant load $q$, because $u(L) = q L^2/(2\, EA) \ne 0$. A traction-free end is a
different boundary condition from a fixed end; with zero end force it is the
[fixed-traction problem](is-fixed-traction-solution.md).
