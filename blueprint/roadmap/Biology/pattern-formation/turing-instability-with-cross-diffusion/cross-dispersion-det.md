# Cross-diffusion dispersion polynomial h(q) = det D q² − b q + det J

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal). The cross-diffusion dispersion polynomial is

$$h(q) = \det D\, q^2 - b\, q + \det J,$$

with the [mixed coefficient](cross-coeff.md)
$b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$. It satisfies
$\det(J - k^2 D) = h(k^2)$ ([determinant of the mode matrix](det-cross-mode-matrix.md)).
