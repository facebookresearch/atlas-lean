# Spreading of Keller–Segel populations in a shifting time-periodic habitat

**Model.** For $N\ge1$, a unit vector $e\in\mathbb S^{N-1}$ and a habitat speed $c\in\mathbb R$, consider

$$u_t=a(t)\Delta u-\eta\chi(t)\nabla\cdot(u\nabla v)+u\,f(t,x\cdot e-ct,u),\qquad \tau v_t=d(t)\Delta v-\nu(t)v+\mu(t)u,\qquad x\in\mathbb R^N,$$

with $T$-periodic Hölder coefficients, $a,d,\nu,\mu>0$, $\chi\ge0$, taxis strength $\eta\ge0$, and a KPP reaction $f$ that depends on space only through the moving coordinate $\xi=x\cdot e-ct$: favorable as $\xi\to-\infty$ with limiting linear growth rate $r_-(t)$ (period mean $\bar r=\langle r_-\rangle>0$), unfavorable ahead of the front, and with time-dependent logistic damping $\beta(t)$. Let $\bar a=\langle a\rangle$ and define the intrinsic KPP speed

$$c_*=2\sqrt{\bar a\,\bar r}.$$

**Theorem (parabolic–elliptic case $\tau=0$).** Assume the damping gap $\delta_0=\min_t(\beta(t)-\gamma_0(t))>0$, where $\gamma_0$ is the explicit taxis-induced coefficient. Then for bounded nonnegative uniformly continuous data there is a unique global classical solution with $0\le u\le\max\{\|u_0\|_\infty,\,r^*/\delta_0\}$, $r^*=\sup_{t,\xi}r(t,\xi)_+$. For nontrivial compactly supported data:

1. if $c<-c_*$, then $\|u(t,\cdot)\|_\infty\to0$ (the habitat recedes faster than the population can spread);
2. if $-c_*<c<c_*$, then for small $\varepsilon>0$, $u\to0$ uniformly on $\{|x|\ge(c_*+\varepsilon)t\}$ and on $\{x\cdot e\ge(c+\varepsilon)t\}$, while $\liminf_t\inf u>0$ on $\{|x|\le(c_*-\varepsilon)t,\ x\cdot e\le(c-\varepsilon)t\}$.

So persistence in a frame moving with velocity $s\in\mathbb R^N$ holds exactly when $|s|<c_*$ and $s\cdot e<c$: the occupied region is the intersection of the KPP spreading cone with the translating favorable half-space. For data occupying the far favorable half-space and vanishing ahead, the longitudinal front moves at $s_c=\min\{c,c_*\}$.

**Moving favorable slab.** If $a\equiv a_0$ is constant and the favorable region is a slab of width $L$ moving at speed $c$, the generalized principal periodic Floquet exponent satisfies

$$\lambda_L(c)=\lambda_L(0)-\frac{c^2}{4a_0},\qquad \lambda_\infty(c)=\lambda_\infty(0)-\frac{c^2}{4a_0}.$$

Hence, when $\lambda_\infty(0)>0$, the critical climate speed is $c_{\mathrm{tr}}=2\sqrt{a_0\lambda_\infty(0)}$: for $|c|<c_{\mathrm{tr}}$ the population persists near the moving slab, while $\lambda_\infty(c)<0$ for $|c|>c_{\mathrm{tr}}$ (extinction then needs an extra weighted-resolvent hypothesis).

## Depends on

- [Fisher–KPP travelling waves](../../pattern-formation/fisher-kpp-travelling-waves/README.md)

## Expansion

The elliptic signal is $v=(\text{Yukawa kernel})*u$, and a first-contact estimate bounds $\nabla\cdot(u\nabla v)$ by a multiple $\gamma_0(t)u^2$ of the density, so the damping gap absorbs the taxis term and gives the $L^\infty$ bound. Upper spreading bounds come from exponential supersolutions $e^{-\lambda(|x|-c_*t)}$ with $\lambda_*=\sqrt{\bar r/\bar a}$, and from the unfavorable region ahead of $\xi=0$; lower bounds use a localized power-Harnack inequality and periodic principal eigenvalue subsolutions in moving balls. The $-c^2/(4a_0)$ shift comes from the Galilean change of variables $\xi=x\cdot e-ct$ and the exponential gauge $e^{-c\xi/(2a_0)}$, which converts the drift into a constant loss.

## Sources

- Hoang-Hung Vo, "Time-Periodic Chemotaxis in Shifting Environments: Propagation and Planar Forced Waves in $\mathbb R^N$", arXiv:2610.36627 (2026), Theorems 1.1–1.3, Proposition 1 and Proposition 3, <https://doi.org/10.48550/arXiv.2610.36627>.
