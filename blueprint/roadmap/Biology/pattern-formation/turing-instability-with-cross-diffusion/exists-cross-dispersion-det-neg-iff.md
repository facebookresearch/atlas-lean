# For det D, det J > 0, h(q) < 0 at some q ≥ 0 iff 2√(det D det J) < b

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal), with $\det D > 0$ and $\det J > 0$. Then the
[dispersion polynomial](cross-dispersion-det.md) $h(q) = \det D\, q^2 - b\, q + \det J$, with
$b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$, is negative at some $q \ge 0$
if and only if $b > 0$ and $4 \det D \det J < b^2$, that is, by the
[squared form of the condition](two-mul-sqrt-lt-cross-coeff-iff.md), if and only if
$2 \sqrt{\det D \det J} < b$.
