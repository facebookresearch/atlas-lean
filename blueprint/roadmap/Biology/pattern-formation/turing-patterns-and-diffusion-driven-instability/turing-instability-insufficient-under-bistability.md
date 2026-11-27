# Turing instability is not sufficient for a patterned state: bistable examples

On $\Omega = [0, L]^N$ ($N = 1, 2$) with periodic boundary conditions let $0 = \rho_0 < \rho_1 \le \rho_2 \le \cdots$ be the eigenvalues of $-\nabla^2$, with eigenfunctions $w_k$. A homogeneous equilibrium is **Turing unstable** if the growth rates $\lambda_k$ of perturbations along $w_k$ satisfy $\Re\lambda_0 < 0$ and $\Re\lambda_k > 0$ for some $k > 0$.

**Keller–Segel with Allee growth.** For

$$\partial_t u = \nabla^2 u - c\nabla\cdot(u\nabla v) + u(b - u)(u - d), \qquad \partial_t v = D\nabla^2 v + u - a v,$$

with $a, c, D > 0$ and $b > d > 0$ (kinetically bistable: $u_0 = 0$ and $u_0 = b$ stable), linearization at $(b, b/a)$ gives growth rates (taking the root with the larger real part)

$$\lambda_k = \tfrac12\Bigl(T_k + \sqrt{T_k^2 - 4Q_k}\Bigr), \quad T_k = -b(b - d) - a - \rho_k(1 + D), \quad Q_k = D\rho_k^2 - \rho_k\bigl(cb - a - Db(b - d)\bigr) + ab(b - d).$$

**Biharmonic model.** For $\partial_t u = -D\nabla^2 u - \nabla^4 u + a u(c - u)(u - b)$ with $a, D > 0$ and $c > b > 0$ (stable $u_0 = 0$ and $u_0 = c$), linearization at $u_0 = c$ gives

$$\lambda_k = D\rho_k - \rho_k^2 + ac(b - c).$$

**Statement (dispersion relations).** Under these positive-parameter assumptions the displayed $\lambda_k$ are the growth rates of the linearisations, and in both models the equilibrium is Turing unstable for suitable parameters; for the biharmonic model, exactly when some $\rho_k$ lies strictly between the roots of $\rho^2 - D\rho + ac(c - b) = 0$, which requires $D^2 > 4ac(c - b)$.

**Numerical observation (not a theorem).** In the source's finite-time simulations from small random perturbations, with randomly drawn Turing-unstable parameters, most runs showed transient patterns that decayed to the *other* stable homogeneous equilibrium, while others ended in patterned states. So linear Turing instability of one equilibrium does not by itself predict that solutions started near it end patterned when the kinetics are multistable. The simulations sample finitely many trajectories over finite times; they do not show that no stable patterned state exists, since such a state may have a basin the sampled trajectories did not enter.

## Expansion

For Keller–Segel, $f(u) = u(b - u)(u - d)$ has $f'(b) = -b(b - d)$; on mode $w_k$ the Jacobian is $\begin{pmatrix} -b(b - d) - \rho_k & cb\rho_k \\ 1 & -a - D\rho_k \end{pmatrix}$, whose trace and determinant are $T_k$ and $Q_k$. For the biharmonic model, $-D\nabla^2 - \nabla^4$ acts on $w_k$ as $D\rho_k - \rho_k^2$ and $g(u) = au(c - u)(u - b)$ has $g'(c) = ac(b - c) < 0$. The linear analysis only predicts initial growth of the unstable modes; the nonlinear dynamics can carry the system into the basin of the other homogeneous equilibrium.

## Sources

- A. L. Krause, E. A. Gaffney, T. J. Jewell et al., "Turing instabilities are not enough to ensure pattern formation", *Bulletin of Mathematical Biology* 86 (2024), <https://doi.org/10.1007/s11538-023-01250-4> (PMC10803432). Section 2, equations (1) and (4)–(7), and the simulation results of Section 3.
