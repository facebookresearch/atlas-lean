# Unique constant coexistence state of the Neumann predator–prey model

Let $\Omega\subset\mathbb{R}^N$ be a bounded $\mathcal C^2$ domain and consider the stationary predator–prey problem with constant kinetic coefficients and no-flux boundary conditions:

$$
\mathscr L_1u=\lambda u-u^2-b\,uv,\qquad \mathscr L_2v=\mu v-v^2+c\,uv\quad\text{in }\Omega,\qquad \partial_{\nu_1}u=\partial_{\nu_2}v=0\ \text{on }\partial\Omega .
$$

Here $\mathscr L_\kappa=-\operatorname{div}(A_\kappa(x)\nabla)+\langle b_\kappa(x),\nabla\rangle$ with $A_\kappa$ uniformly elliptic and symmetric, **arbitrary** transport fields $b_\kappa\in(L^\infty(\Omega))^N$, and $\nu_\kappa=A_\kappa n$ the conormal. $b,c>0$ are constants (after rescaling $U=u/\alpha$, $V=v/\delta$ of a model with crowding coefficients $\alpha,\delta$, the new constants are $b=\beta/\delta$, $c=\gamma/\alpha$), and $\lambda,\mu\in\mathbb{R}$. Since $\sigma_0[\mathscr L_\kappa,\partial_{\nu_\kappa},\Omega]=0$, coexistence states exist iff

$$
\lambda>b\mu\quad\text{and}\quad \mu>-c\lambda,
$$

and then the system has the constant coexistence state

$$
u_c=\frac{\lambda-b\mu}{1+bc},\qquad v_c=\frac{\mu+c\lambda}{1+bc}.
$$

**Theorem.** If $bc<1$, then $(u_c,v_c)$ is the unique coexistence state. More precisely, for $n\ge1$ let

$$
\underline z_n=(\lambda-b\mu)\sum_{j=0}^{2n-1}(-bc)^j,\quad \overline z_n=(\lambda-b\mu)\sum_{j=0}^{2n}(-bc)^j,\quad
\underline w_n=(\mu+c\lambda)\sum_{j=0}^{2n-1}(-bc)^j,\quad \overline w_n=(\mu+c\lambda)\sum_{j=0}^{2n}(-bc)^j .
$$

Then every coexistence state $(u,v)$ satisfies $\underline z_n\ll u\ll\overline z_n$ and $\underline w_n\ll v\ll\overline w_n$ for all $n$. Both pairs of bounds converge to $(u_c,v_c)$ as $n\to\infty$.

## Depends on

- [Existence and local uniqueness of coexistence states of diffusive predator–prey models](existence-and-local-uniqueness-of-coexistence-states.md)

## Expansion

Under Neumann conditions, the logistic problem $\mathscr L_\kappa w=\rho w-w^2$ has the constant solution $w=\rho$ for $\rho>0$, even with transport terms, because constants lie in the kernel of $\mathscr L_\kappa$. Every coexistence state is positive on $\bar\Omega$, and the bounds are built by alternating between the two equations: each new bound for one species comes from comparing it with a constant sub- or supersolution of a logistic problem whose growth rate involves the previous bound for the other species. This adapts the monotone scheme of the symmetric case. The bounds are $\lambda-b\mu$ and $\mu+c\lambda$ times partial sums of the geometric series $\sum(-bc)^j$, which converges, to $1/(1+bc)$, exactly when $bc<1$. Energy methods for the self-adjoint case ($b_1=b_2=0$) do not apply to non-self-adjoint operators; this monotone squeezing argument does. The constant-coefficient condition $bc<1$ corresponds to $\beta\gamma<\alpha\delta$ in the original constants.

## Sources

- J. López-Gómez, E. Muñoz-Hernández, "Uniqueness of coexistence states in diffusive predator-prey models, at the occasion of the 100th anniversary of the first publication of V. Volterra on the predator-prey system", arXiv preprint (2026), Section 7 (Theorem 7.4 and the setup of Section 7), <https://doi.org/10.48550/arXiv.2611.24855>.
