# Classical solution of the linearized cross-diffusion system

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal). A function
$w : \mathbb{R} \times \mathbb{R} \to \mathbb{C}^2$ is a classical solution of the linearized system
$w_t = D w_{xx} + J w$ on $\mathbb{R} \times \mathbb{R}$ when there are $w_x, w_{xx}$ such that, for
all $t$ and $x$, $w(t, \cdot)$ has derivative $w_x(t, x)$ at $x$, $w_x(t, \cdot)$ has derivative
$w_{xx}(t, x)$ at $x$, and $w(\cdot, x)$ has derivative $D\, w_{xx}(t, x) + J\, w(t, x)$ at $t$.
