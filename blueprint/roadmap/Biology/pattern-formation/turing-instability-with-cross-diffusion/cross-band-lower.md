# Lower end (b − √Δ)/(2 det D) of the cross-diffusion unstable band

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal). The lower end of the unstable band of squared
wavenumbers is

$$q_- = \frac{b - \sqrt{\Delta}}{2 \det D},$$

with $b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$ and the
[band discriminant](cross-band-discriminant.md) $\Delta = b^2 - 4 \det D \det J$. The square root is
read as $0$ for $\Delta < 0$, and the quotient as $0$ when $\det D = 0$. It is meaningful for
$\det D > 0$ and $\Delta > 0$, when it is the smaller root of the
[dispersion polynomial](cross-dispersion-det.md).
