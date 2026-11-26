# Unique coexistence state of the symmetric diffusive predator–prey model

Let $\Omega\subset\mathbb{R}^N$ be a bounded $\mathcal C^2$ domain, $\mathscr L$ a uniformly elliptic operator and $\mathscr B$ a mixed boundary operator (Dirichlet on part of $\partial\Omega$, Robin of either sign on the rest). Consider the **symmetric** predator–prey problem, where prey $u$ and predator $v$ share the same diffusion operator, boundary conditions and growth rate $\lambda$:
$$
\mathscr Lu=\lambda u-a(x)u^2-b(x)uv,\qquad \mathscr Lv=\lambda v-d(x)v^2+c(x)uv\quad\text{in }\Omega,\qquad \mathscr Bu=\mathscr Bv=0\ \text{on }\partial\Omega,
$$
with $a,b,c,d\in\mathcal C(\bar\Omega)$, $a,d>0$, $b,c\ge0$, $b\ne0\ne c$. Write $\theta_{[\mathscr L,\lambda,\xi]}$ for the unique positive solution of $\mathscr Lw=\lambda w-\xi w^2$, $\mathscr Bw=0$, which exists iff $\lambda>\sigma_0[\mathscr L,\mathscr B,\Omega]$. Assume the coexistence condition
$$
\lambda=\sigma_0\bigl[\mathscr L+d\,\theta_{[\mathscr L,\lambda,d]},\mathscr B,\Omega\bigr]>\sigma_0\bigl[\mathscr L+b\,\theta_{[\mathscr L,\lambda,d]},\mathscr B,\Omega\bigr],
$$
which holds in particular when $b\lneq d$. Under this condition a coexistence state exists.

**Theorem (uniqueness and stability).** Suppose $\dfrac{d-b}{a+c}$ is a positive constant. Then every coexistence state satisfies $u=\frac{d-b}{a+c}\,v$, and the unique coexistence state is
$$
(u_\lambda,v_\lambda)=\Bigl(\theta_{[\mathscr L,\lambda,\frac{ad+bc}{d-b}]},\ \tfrac{a+c}{d-b}\,\theta_{[\mathscr L,\lambda,\frac{ad+bc}{d-b}]}\Bigr).
$$
If in addition $b$ and $c$ are constant, $(u_\lambda,v_\lambda)$ is non-degenerate and locally asymptotically stable for the parabolic problem $\partial_tu+\mathscr Lu=\lambda u-au^2-buv$, $\partial_tv+\mathscr Lv=\lambda v-dv^2+cuv$.

**Theorem (global attraction, constant coefficients).** Let $a,b,c,d$ be positive constants. After rescaling to $\mathscr Lu=\lambda u-u^2-buv$, $\mathscr Lv=\lambda v-v^2+cuv$ (with new $b=B/D$, $c=C/A$), coexistence requires $b<1$ and $\lambda>\sigma_0[\mathscr L,\mathscr B,\Omega]$. The coexistence state is then
$$
u_\lambda=\frac{1-b}{1+bc}\,\theta_{[\mathscr L,\lambda]},\qquad v_\lambda=\frac{1+c}{1+bc}\,\theta_{[\mathscr L,\lambda]},
$$
where $\theta_{[\mathscr L,\lambda]}$ solves $\mathscr Lw=\lambda w-w^2$. If moreover $bc<1$ (equivalently $BC<AD$ in the original constants), then $(u_\lambda,v_\lambda)$ attracts every solution of the parabolic problem with nonnegative, nontrivial initial data in both components.

## Depends on

- [Existence and local uniqueness of coexistence states of diffusive predator–prey models](existence-and-local-uniqueness-of-coexistence-states.md)

## Expansion

For a coexistence state $(u,v)$, $\lambda$ is the principal eigenvalue of both $\mathscr L+au+bv$ and $\mathscr L+dv-cu$. When $(d-b)/(a+c)$ is a positive constant, this forces the potentials to agree for $u=\frac{d-b}{a+c}v$, so the system collapses to one logistic equation with effective crowding coefficient $\frac{ad+bc}{d-b}$, which has a unique positive solution. With $bc<1$, an alternating monotone scheme of logistic problems ($\overline u_n=\theta_{[\mathscr L+b\underline v_n,\lambda]}$, $\overline v_n=\theta_{[\mathscr L-c\overline u_n,\lambda]}$, and so on) squeezes every solution between sub- and supersolutions converging to $(u_\lambda,v_\lambda)$. Run along the parabolic flow, the same scheme gives global attraction. This is sharp: for some non-constant coefficients the unique coexistence state can lose stability through a Hopf bifurcation.

## Sources

- J. López-Gómez, E. Muñoz-Hernández, "Uniqueness of coexistence states in diffusive predator-prey models, at the occasion of the 100th anniversary of the first publication of V. Volterra on the predator-prey system", arXiv preprint (2026), Section 6 (Proposition 6.1, Theorems 6.2, 6.4 and 6.5, Corollary 6.3), <https://doi.org/10.48550/arXiv.2611.24855>.
