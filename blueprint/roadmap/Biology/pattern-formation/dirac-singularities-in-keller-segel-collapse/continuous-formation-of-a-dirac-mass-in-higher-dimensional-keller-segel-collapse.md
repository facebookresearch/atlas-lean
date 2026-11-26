# Continuous formation of a Dirac mass in higher-dimensional Keller–Segel collapse

**Model.** Let $n\ge3$, $\Omega=B_R(0)\subset\mathbb R^n$ and consider the parabolic–elliptic Keller–Segel system with homogeneous Neumann conditions

$$u_t=\Delta u-\nabla\cdot(u\nabla v),\qquad 0=\Delta v-\mu+u,$$

for radially symmetric continuous initial data $u_0\ge0$ with $\int_\Omega u_0=m>0$, where $\mu=\frac{mn}{\omega_nR^n}$ is the spatial average and $\omega_n=n|B_1(0)|$. In the accumulated-mass variable $s=|x|^n$ set

$$w_0(s)=\int_0^{s^{1/n}}\sigma^{n-1}u_0(\sigma)\,d\sigma,\qquad s\in[0,R^n].$$

**Theorem.** There is a minimal, mass-conserving, radially symmetric measure-valued solution defined for all $t\ge0$ of the form

$$u(t)=\theta(t)\,\delta_0+\rho(\cdot,t)\,dx,$$

with $\rho\ge0$ continuous away from the origin and $\theta\ge0$ bounded, nondecreasing and right-continuous. Moreover, for every $\gamma\in(0,1-\tfrac2n)$, $c>0$, $\tau>0$ and $\eta>0$ there is $\delta>0$ such that if

$$w_0(s)\ge c\,\frac{s^2}{s^{2-\gamma}+\delta}\qquad\text{for all }s\in[0,R^n],$$

then for some $t_0\in(0,\tau)$

$$0<\theta(t_0)<\eta,$$

$\theta$ is strictly increasing on $[t_0,\infty)$, and $\theta(t)\to m$ as $t\to\infty$.

So in dimensions $n\ge3$ a singular point mass forms, but unlike the two-dimensional case (where a positive amount of mass, at least $8\pi$, concentrates at once) the Dirac weight starts from zero and grows continuously, and eventually the whole population is absorbed at the origin.

## Expansion

In the variable $s=r^n$ the radial problem becomes a scalar degenerate parabolic equation for the accumulated mass $w(s,t)$, for which a comparison principle holds. The minimal solution is obtained as a monotone limit of regularized problems; $w(0,t)=\lim_{s\downarrow0}w(s,t)$ is then well defined and, up to the factor $\omega_n$, equals the Dirac weight $\theta(t)$. A subsolution adapted to data that are concentrated near the origin (the condition $w_0\gtrsim s^2/(s^{2-\gamma}+\delta)$, with $\delta$ small) shows that $w(0,t)$ becomes positive at some small time while still small. Once $\inf_s w(s,t_0)>0$, a further comparison argument shows that $w(0,\cdot)$ is strictly increasing and converges to $m/\omega_n$, which means total absorption of mass.

## Sources

- Gregor Flüchter, "Formation and Behavior of Dirac Singularities in the Parabolic-Elliptic Keller-Segel System in Dimensions $n\geq 3$", arXiv:2605.00110 (2026), Theorem 1.2, Propositions 1.3–1.4 and Corollary 3.6, <https://doi.org/10.48550/arXiv.2605.00110>.
