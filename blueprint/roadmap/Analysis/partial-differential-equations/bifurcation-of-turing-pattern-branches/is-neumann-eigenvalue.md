# Neumann eigenvalue of the linearized system on an interval

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u, d_v$ be real and
$D = \operatorname{diag}(d_u, d_v)$, and let $L$ be real. A complex number $\mu$ is a Neumann
eigenvalue when it is an eigenvalue of the
[mode matrix](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md)
$J - k_n^2 D$ for some $n \in \mathbb{N}$, where $k_n$ are the
[Neumann wavenumbers](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md)
$k_n = n\pi/L$ ($n \in \mathbb{N}$, all $0$ when $L = 0$): $(J - k_n^2 D)\, v = \mu v$ for some
nonzero $v \in \mathbb{C}^2$.

For $L > 0$ these are the eigenvalues that the zero-flux Fourier modes $\cos(k_n x)\, v$ give to the
linearization $w \mapsto D w_{xx} + J w$ on $[0, L]$ with homogeneous Neumann boundary conditions;
that they are all its eigenvalues rests on the completeness of the cosine modes, which the
definition does not involve. Only the discrete wavenumbers $k_n$ enter, not every real wavenumber.
The definition is meaningful for $L > 0$: at $L = 0$ every $k_n$ is $0$, so the Neumann eigenvalues
are the eigenvalues of $J$, and for $L < 0$ they are those for $-L$, since only $k_n^2$ enters.

In the model $d_u, d_v > 0$; the definition is stated for all real values.
