# Unique globally stable oxygen profile in a core–shell transplant

**Setting.** Transplanted cells occupy a core $\Omega_1$ surrounded by a protective shell $\Omega_2$; $\Omega=\Omega_1\cup\Gamma\cup\Omega_2\subset\mathbb R^N$ ($N\ge2$, $N=3$ in applications) is bounded, $\Gamma=\partial\Omega_1$ is a closed connected $C^2$ hypersurface and $S=\partial\Omega$ is the outer boundary. After a linear change of variables the non-dimensional oxygen variable $u$ satisfies

$$\partial_tu-b\,\Delta u=\mathbb 1_{\Omega_1}\varphi(u)\quad\text{in }(\Omega\setminus\Gamma)\times(0,T),\qquad u|_S=0,\qquad [u]_\Gamma=0,\qquad [b\,\nabla u\cdot\nu]_\Gamma=0,$$

with piecewise constant diffusivity $b=b_1$ in $\overline\Omega_1$, $b=b_2$ in $\Omega_2$ ($b_1,b_2>0$), a Dirichlet condition expressing a stable oxygen supply outside, continuity of concentration and flux across $\Gamma$, and Michaelis–Menten consumption only in the core,

$$\varphi(z)=\begin{cases}\dfrac{c_0-z}{c_1-z},& z\le c_0,\\[4pt] 0,& z>c_0,\end{cases}\qquad 0<c_0<c_1,$$

where $z>c_0$ corresponds to zero oxygen (cells dying from hypoxia, no consumption). The function $\varphi$ is decreasing, takes values in $[0,1)$, is Lipschitz with constant $1/(c_1-c_0)$, and satisfies $z\varphi(z)\le c_0$.

Let $V=H^1_0(\Omega)$, $H=L^2(\Omega)$, $A(u)=-b\Delta u-\mathbb 1_{\Omega_1}\varphi(u)$ with domain $D(A)$ of $u\in V$ that are $H^2$ on each $\Omega_i$ and satisfy the flux condition.

**Theorem.**
1. (Well-posedness) For $u_0\in D(A)$ the problem $u'+A(u)=0$ has a unique solution $u\in C^0([0,T];H)\cap\mathrm{Lip}(0,T;D(A))$ with $u'\in C_w(0,T;H)$ for every $T>0$, depending continuously on $u_0$ in $D(A)$.
2. (Uniqueness of the steady state) There is exactly one stationary solution $u^*$.
3. (Global exponential stability) For every solution there is $\beta>0$ with

$$\lim_{t\to\infty}e^{\beta t}\,\|u(t)-u^*\|_{L^2(\Omega)}=0,$$

and $u(t)\rightharpoonup u^*$ weakly in $H^1_0(\Omega)$.

## Expansion

Because $\varphi$ is decreasing, $-\mathbb 1_{\Omega_1}\varphi$ is monotone, so $A$ is a maximal monotone operator on $H$ and the Kōmura–Kato theory of monotone evolution equations gives part 1. Stationary solutions are the critical points of the energy

$$E(u)=\frac12\int_\Omega b\,|\nabla u|^2\,dx-\int_{\Omega_1}\Phi(u)\,dx,\qquad \Phi'=\varphi,$$

whose derivative $E'$ is strongly monotone on $V$ (Poincaré's inequality controls the concave part), so $E$ has a unique critical point, its global minimizer. Testing the difference $u-u^*$ against itself and using monotonicity of $-\varphi$ with Poincaré's inequality gives $\frac{d}{dt}\|u-u^*\|_H^2\le-2\lambda_1\min(b_1,b_2)\|u-u^*\|_H^2$, hence exponential decay; boundedness in $V$ then yields weak convergence there.

## Sources

- T. G. de Jong, G. Prokert, A. E. Sterk, "Reaction-diffusion transport into core-shell geometry: Well-posedness and stability of stationary solutions", arXiv:2305.03397 (2023), model (1)–(5) with (6)–(7), Lemma 1, Theorem 2, Lemmas 3–4, Theorems 5–6 and Corollary 7, <https://doi.org/10.48550/arXiv.2305.03397>.
