# Strict monotonicity and domain limits of the spectral bound for cooperative nonlocal dispersal

**Setting.** For $m$ interacting populations (or infection classes) with dispersal rates $d_1,\dots,d_m>0$ on a bounded domain $\Omega\subset\mathbb R^n$, consider the cooperative nonlocal dispersal operator on $[C(\overline\Omega)]^m$
$$\mathcal J_{A,\Omega}[\varphi]_i(x)=d_i\int_\Omega J_i(x,y)\varphi_i(y)\,dy+\sum_jA_{ij}(x)\varphi_j(x),\qquad x\in\overline\Omega,$$
with nonnegative continuous kernels and a continuous matrix field $A(x)$ that is cooperative (nonnegative off-diagonal entries) and irreducible at some point of $\Omega$. Let $s(\cdot)$ denote the spectral bound and $s(A,\overline\Omega)=\max_{x\in\overline\Omega}s(A(x))$. A real eigenvalue with a componentwise positive eigenfunction is a *principal eigenvalue*; unlike for local diffusion, it need not exist, because the multiplication part is not compact.

**Existence and characterization.** Always $s(\mathcal J_{A,\Omega})\ge s(A,\overline\Omega)$, and $s(\mathcal J_{A,\Omega})$ is the limit of principal eigenvalues of operators with slightly perturbed coefficients $A^\pm_\epsilon\to A$. If
$$\int_\Omega\frac{dx}{s(A,\overline\Omega)-s(A(x))}=\infty$$
(for instance if $s(A(x))$ is constant and maximal on an open set, or in one dimension if $s(A(\cdot))$ is locally Lipschitz near a maximum point), then $s(\mathcal J_{A,\Omega})>s(A,\overline\Omega)$ and it is a principal eigenvalue. Without a principal eigenvalue, $s(\mathcal J_{A,\Omega})=s(A,\overline\Omega)$.

**Theorem (strict comparison).**

1. If $A\ge B$, $A\not\equiv B$, and at least one of $s(\mathcal J_{A,\Omega})$, $s(\mathcal J_{B,\Omega})$ is a principal eigenvalue, then $s(\mathcal J_{A,\Omega})>s(\mathcal J_{B,\Omega})$.
2. If $\Omega_1\subset\Omega_2$ with $|\Omega_2\setminus\Omega_1|>0$ and at least one of the two spectral bounds is a principal eigenvalue, then $s(\mathcal J_{A,\Omega_1})<s(\mathcal J_{A,\Omega_2})$.

Without principal eigenvalues, strict monotonicity can fail.

**Theorem (small and large domains).** If $x_0$ is an irreducibility point, $s(\mathcal J_{A,B_\sigma(x_0)})\to s(A(x_0))$ as $\sigma\to0$. If the kernels are even convolution kernels $J_i(x,y)=K_i(y-x)$, $A(x)\le A^\infty$ for a constant cooperative irreducible $A^\infty$, and $A\to A^\infty$ uniformly on cubes of side $l_k\to\infty$, then
$$\lim_{l\to\infty}s(\mathcal J_{A,B_l(0)})=s(A^\infty+D),\qquad D=\operatorname{diag}(d_i).$$
Consequently, if $s(A(0))<0<s(A^\infty+D)$, there is a unique critical habitat size $l_*$ at which the spectral bound of the linearization crosses zero: for a two-class heterogeneous epidemic model on $(0,l)$, the infection dies out for $l\le l_*$ and persists for $l>l_*$; for a scalar nonlocal free-boundary model with front $h(t)$, spreading occurs whenever $h_0\ge l_*$, vanishing forces $h(\infty)\le l_*$, and for $h_0<l_*$ there is a sharp expansion-rate threshold $\mu^*$ separating vanishing from spreading.

## Expansion

When a principal eigenfunction $u\gg0$ exists for one operator, comparison is done with the sliding argument: take $t=\max v_i/u_i$ for the other operator's eigenfunction (or a perturbed one) and apply a strong maximum principle to $tu-v$, which forces strict inequality unless $A\equiv B$. In the absence of a principal eigenvalue, the spectral bound equals the essential part $s(A,\overline\Omega)$, which is insensitive to small changes of the domain away from the maximizing points; this is exactly where strict monotonicity breaks down. The large-domain limit uses test functions spread over the cubes where $A\approx A^\infty$, for which $\int K_i\approx1$ produces the shift by $D$.

## Sources

- Mingxin Wang, Lei Zhang, "Spectral bounds of cooperative nonlocal dispersal systems: monotonicity, domain limits, and applications", arXiv:2611.33573 (2026), Theorems 1.1, 1.2 and 2.1, Proposition 2.1, Corollaries 2.1, 3.1–3.2, Proposition 3.1, Proposition 5.1 and Theorem 6.1, <https://doi.org/10.48550/arXiv.2611.33573>.
