# Auxostat feedback stabilization of a trait-structured chemostat

**Model.** Let $\Omega\subset\mathbb{R}^d$ be a bounded domain with $C^1$ boundary and outward normal $\vec n$. A population density $f(t,z)$ structured by a trait $z\in\Omega$ grows on a substrate $s(t)$ fed at concentration $s_{in}>0$, with dilution rate $u(t)\ge0$ and mutation rate $\alpha\ge0$:

$$
\begin{aligned}
\partial_t f(t,z)&=\bigl(\mu(s(t),z)-u(t)\bigr)f(t,z)+\alpha\Delta_z f(t,z), && t>0,\ z\in\Omega,\\
\dot s(t)&=-\int_\Omega \mu(s(t),z')f(t,z')\,dz'+u(t)\bigl(s_{in}-s(t)\bigr), && t>0,\\
\partial_{\vec n}f(t,z)&=0, && z\in\partial\Omega .
\end{aligned}
$$

The kinetics satisfy: $\mu\in C^1_{loc}(\mathbb{R}_+,C^1(\Omega))$, $\mu(s,\cdot)$ bounded and Lipschitz for $s>0$, $\mu(s,z)>0$ for $s>0$, $\mu(0,z)=0$; $\sup_z\mu(s,z)\le\hat\mu s$ for some $\hat\mu>0$; and $\mu(\cdot,z)$ is Lipschitz on bounded intervals uniformly in $z$. For an admissible control (measurable, values in $[0,u_{max}]$), or a feedback control $u(t)=R[f(t,\cdot),s(t)]$, and data $s_0\in(0,s_{in})$, $0\le f_0\in L^1(\Omega)$, the system has a unique positive mild solution with $s$ valued in $[0,s_{in}]$ and $f\in C(\mathbb{R}_+,L^1(\Omega))$ (classical if $u$ is continuous).

**Auxostat-type controls.** For $\sigma\in(0,s_{in})$ consider

$$
\text{(i) } u=\frac{\int_\Omega\mu(s,z)f\,dz}{s_{in}-s},\quad \text{(ii) } u=\frac{\int_\Omega\mu(s,z)f\,dz}{s_{in}-\sigma},\quad \text{(iii) } u=\frac{\int_\Omega\mu(\sigma,z)f\,dz}{s_{in}-s},\quad \text{(iv) } u=\frac{\int_\Omega\mu(\sigma,z)f\,dz}{s_{in}-\sigma}.
$$

For a level $\bar s$ let $\varphi_{\bar s}>0$ be a principal eigenfunction of $\alpha\Delta\varphi+\mu(\bar s,\cdot)\varphi=-\lambda\varphi$ in $\Omega$, $\partial_{\vec n}\varphi=0$ on $\partial\Omega$.

**Theorem A (control (i)).** Let $\alpha>0$, $s_0>0$ and $f_0\ge0$ nonzero. Under control (i), $s(t)=s_0$ for all $t\ge0$ and, for every $1\le p<\infty$,

$$
\lim_{t\to\infty}\Bigl\|f(t,\cdot)-\frac{s_{in}-s_0}{\|\varphi_{s_0}\|_1}\varphi_{s_0}\Bigr\|_p=0 .
$$

**Theorem B (controls (ii)–(iv)).** Let $\alpha>0$ and $\sigma\in(0,s_{in})$, and assume one of: control (ii) with $\inf_z\mu(s,z)>0$ for every $s>0$; control (iii) with $\inf_z\partial_s\mu(s,z)>0$ for every $s\ge0$; control (iv) with $\mu(\cdot,z)\in C^2$ strictly concave on $[0,s_{in}]$. Then

$$
(\bar s,\bar f)=\Bigl(\sigma,\ (s_{in}-\sigma)\frac{\varphi_\sigma}{\|\varphi_\sigma\|_1}\Bigr)
$$

is the unique stationary solution under that control, and for every $s_0>0$ and nonzero $f_0\ge0$, $\|f(t,\cdot)-\bar f\|_p\to0$ for all $1\le p<\infty$.

## Depends on

- [Chemostat equilibria and the washout threshold](../chemostat/chemostat-equilibria-and-washout.md)

## Expansion

With control (iii), $s=\sigma$ is invariant ($\dot s=0$ once $s=\sigma$), so the substrate is regulated at the set-point, which is the defining feature of an auxostat; under (i) the substrate is frozen at its initial value. Once $s$ is fixed at $\bar s$, the density obeys a linear equation $\partial_tf=(\mu(\bar s,\cdot)-u)f+\alpha\Delta f$ whose normalized solutions converge to the principal eigenfunction by Krein–Rutman theory, while the substrate balance forces total biomass $\|f\|_1=s_{in}-\bar s$. For (ii)–(iv) the substrate is not frozen, and the extra hypotheses give monotonicity or concavity estimates showing $s(t)\to\sigma$ before the same spectral argument applies. The limit is then independent of the initial condition, which makes (ii)–(iv) the useful controls for steering.

## Sources

- Claudia Alvarez-Latuz, Térence Bayen, Jérôme Coville, *Target controllability for a minimum time problem in a trait-structured chemostat model*, arXiv (2026). Theorems 1.1, 1.3 (well-posedness), Theorem 1.4 (control (i)), Theorem 1.5 (controls (ii)–(iv)); Hypotheses in Section 1. <https://doi.org/10.48550/arXiv.2602.21999>
