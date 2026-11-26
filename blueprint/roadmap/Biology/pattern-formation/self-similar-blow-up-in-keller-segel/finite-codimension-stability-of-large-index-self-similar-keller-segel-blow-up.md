# Finite-codimension stability of large-index self-similar Keller–Segel blow-up

**Model.** The parabolic–elliptic Keller–Segel system in $\mathbb{R}^3$,
$$u_t=\Delta u-\nabla\cdot(u\nabla\Phi_u),\qquad 0=\Delta\Phi_u+u,\qquad (x,t)\in\mathbb{R}^3\times(0,T),$$
models the density $u\ge 0$ of cells attracted by a chemical $\Phi_u$ they produce. A self-similar blow-up solution has the form $u(t,x)=(T-t)^{-1}U\big(x/\sqrt{T-t}\big)$, where $U$ solves
$$\Delta U-\tfrac12\, y\cdot\nabla U-U+\nabla U\cdot\nabla\Delta^{-1}U+U^2=0 .$$

**Profile family.** There is $n_*$ such that for every $n\ge n_*$ the radial mass-variable equation $\Phi''+(4/r-r/2)\Phi'-\Phi+6\Phi^2+2r\Phi\Phi'=0$ has a smooth positive decreasing radial solution $\Phi_n$, and $U_n:=6\Phi_n+2r\Phi_n'$ is a radial self-similar profile. The number $N_n$ of (simple) zeros of $\Lambda\Phi_n$ satisfies $N_n=n+N_0$ for an integer $N_0$ independent of $n$.

**Spectral theorem.** For $n$ large, the linearized operator $L_n$ around $U_n$ has exactly $N_n$ simple negative eigenvalues $-\mu_{1,n}<\dots<-\mu_{N_n,n}<-1$ with radial eigenfunctions $\phi_{j,n}$; apart from these, its spectrum in $\{\Re z<0\}$ consists only of the scaling eigenvalue $-1$ (eigenvector $\Lambda U_n$) and the translation eigenvalue $-\tfrac12$ (eigenvectors $\partial_iU_n$, $i=1,2,3$). In every spherical-harmonic sector $l\ge 2$ the real part of the spectrum is bounded below by $\tfrac14$, and this bound is sharp.

**Stability theorem.** For $n$ large there are $\delta_n>0$ and a Lipschitz map $c_n:V_n\cap B(0,\delta_n)\to\mathbb{R}^{N_n}$, $c_n(0)=0$, on the stable complement $V_n$ such that for every small perturbation $v_0\in V_n$ the solution with data
$$u_0=U_n+v_0+\sum_{j=1}^{N_n}c_{j,n}(v_0)\phi_{j,n}$$
blows up at a finite time $T$ with type I rate:
$$u(t,x)=\frac{1}{T-t}\Big[U_n\Big(\frac{x-x(t)}{\sqrt{T-t}}\Big)+\tilde u\Big(t,\frac{x-x(t)}{\sqrt{T-t}}\Big)\Big],\qquad \|\tilde u(t)\|_{H^2(\mathbb{R}^3)}\to 0,\ \ x(t)\to x_* .$$
When translations and dilations are also allowed, the set of initial data with this blow-up behavior is locally a Lipschitz graph of codimension exactly $N_n$, the number of intrinsic unstable radial modes. No symmetry is imposed on the perturbation.

## Expansion

The profiles are built by inner–outer matching: an inner core rescaled by $\mu_n\to 0$ glued to the singular steady state $r^{-2}$ with a small oscillatory correction, whose $\sin(\omega_*\log s)$ tail produces one new zero of $\Lambda\Phi_n$ per index, giving $N_n=n+N_0$. In the radial sector a reduced-mass transformation turns the nonlocal non-self-adjoint operator into a local Sturm–Liouville problem, so the negative eigenvalues are counted by Sturm oscillation; the $l=1$ sector contains only the translation modes, and $l\ge 2$ sectors are uniformly stable. Modulation equations for $(T,x(t))$, higher-order energy estimates, and a Brouwer fixed-point argument on the $N_n$ unstable coefficients then close the nonlinear argument.

## Sources

- Te Li, Yuwei Sun and Kaiqiang Zhang, "Nonradial stability of an infinite family of self-similar blow-up profiles for the three-dimensional Keller--Segel equation", arXiv:2609.06479 (2026), Proposition 1.1, Theorems 1.2–1.3 and Corollary 1.5, <https://doi.org/10.48550/arXiv.2609.06479>.
