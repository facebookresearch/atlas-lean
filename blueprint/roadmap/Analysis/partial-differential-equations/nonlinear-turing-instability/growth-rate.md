# Growth rate of a Fourier mode: the largest real part of an eigenvalue

Let $J$ be a real $2 \times 2$ matrix (the Jacobian of the kinetics at a steady state), let
$d_u, d_v$ and $k$ be real, let $D = \operatorname{diag}(d_u, d_v)$, and let $\tau$ and $\delta$ be
the trace and the determinant of the
[mode matrix](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md)
$J - k^2 D$. The growth rate of the Fourier mode of wavenumber $k$ is

$$\lambda = \frac{\tau + \sqrt{\tau^2 - 4\delta}}{2},$$

where $\sqrt{x}$ is read as $0$ for $x < 0$. When $\tau^2 - 4\delta \ge 0$ it is the larger root of
the characteristic polynomial $\mu^2 - \tau\mu + \delta$, a real eigenvalue of $J - k^2 D$. When
$\tau^2 - 4\delta < 0$ the eigenvalues are complex conjugates with real part $\tau/2$, and the
formula gives that common real part, which is not an eigenvalue. In both cases $\lambda$ is the
largest real part of an eigenvalue of $J - k^2 D$. When $\delta < 0$ the growth rate is a positive
eigenvalue with a real eigenvector; this is the case of every unstable mode when
$\operatorname{tr} J < 0$ and $d_u, d_v \ge 0$.

In the model $d_u, d_v > 0$; the definition holds for all real values.
