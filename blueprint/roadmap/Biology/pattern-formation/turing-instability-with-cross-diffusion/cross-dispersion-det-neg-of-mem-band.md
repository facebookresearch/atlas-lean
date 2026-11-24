# For det D > 0, h(q) < 0 for every q strictly inside the band (q₋, q₊)

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal), with $\det D > 0$, and let $q$ be real with
$q_- < q < q_+$, where $q_\mp = (b \mp \sqrt{\Delta})/(2 \det D)$ are the
[lower](cross-band-lower.md) and [upper](cross-band-upper.md) band ends, with
$b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$ and
$\Delta = b^2 - 4 \det D \det J$. Then $h(q) < 0$ for the
[dispersion polynomial](cross-dispersion-det.md) $h(q) = \det D\, q^2 - b\, q + \det J$. When
$\Delta < 0$ the square root is read as $0$, so $q_- = q_+$ and no $q$ qualifies.
