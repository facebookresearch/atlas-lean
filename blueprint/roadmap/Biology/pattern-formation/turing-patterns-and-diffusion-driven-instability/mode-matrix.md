# Mode matrix of a linearized reaction-diffusion system

Let $J$ be a real $2 \times 2$ matrix, the Jacobian of the kinetics at a steady state, with $J_{ij}$ the
partial derivative of the $i$-th reaction term with respect to the $j$-th species, so
$J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$, and let $d_u, d_v, k$ be real. The mode
matrix of wavenumber $k$ is $J - k^2 D$, with $D = \operatorname{diag}(d_u, d_v)$ the
[diffusion matrix](diffusion-matrix.md); it governs the Fourier mode of wavenumber $k$ of the
linearized system $w_t = D w_{xx} + J w$.
