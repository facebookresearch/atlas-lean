# Inviscid limit of the Keller–Segel equations with logistic sensitivity

**Setting.** On $\mathbb R^d$, $d\ge1$, compare the parabolic Keller–Segel system with logistic sensitivity and diffusion $\varepsilon\in(0,1]$,

$$\partial_tu^\varepsilon-\varepsilon\Delta u^\varepsilon+\nabla\cdot\big(u^\varepsilon(1-u^\varepsilon)\nabla S^\varepsilon\big)=0,\qquad (I-\Delta)S^\varepsilon=u^\varepsilon,$$

with the hyperbolic Keller–Segel system ($\varepsilon=0$)

$$\partial_tu+\nabla\cdot\big(u(1-u)\nabla S\big)=0,\qquad (I-\Delta)S=u,$$

both started from the same datum $u_0$.

**Theorem (critical Besov spaces).**

1. If $1<p<\infty$ and $u_0\in B^{1+d/p}_{p,1}(\mathbb R^d)$, there is $T>0$ independent of $\varepsilon$ such that both systems have unique solutions in $C([0,T];B^{1+d/p}_{p,1})$ and

$$\|u^\varepsilon-u^0\|_{L^\infty_TB^0_{p,1}}\le C\begin{cases}\varepsilon,&p\le d,\\ \varepsilon^{(1+d/p)/2},&p>d.\end{cases}$$

2. If $u_0\in B^1_{\infty,1}(\mathbb R^d)$, then on a common existence interval

$$\|u^\varepsilon-u^0\|_{L^\infty_TL^\infty}\le C\varepsilon^{1/2},\qquad \|u^\varepsilon-u^0\|_{L^\infty_TB^0_{\infty,1}}\le C\varepsilon^{1/2}\Big(1+\log\big(e+C\varepsilon^{-1/2}\big)\Big),$$

and $u^\varepsilon\to u^0$ strongly in $L^\infty(0,T;B^1_{\infty,1})$.
3. The exponent $1/2$ is optimal up to logarithms: there is a fixed $u_0\in B^1_{\infty,1}$ such that for every $t_*\in(0,T]$

$$\frac{c_{t_*}\,\varepsilon^{1/2}}{[\log(e/\varepsilon)]^2}\le\|u^\varepsilon(t_*)-u^0(t_*)\|_{L^\infty}\le C\varepsilon^{1/2}$$

for all small $\varepsilon$.

## Expansion

Writing $S=(I-\Delta)^{-1}u$, the flux becomes a transport term $(1-2u)\nabla S\cdot\nabla u$ plus a zero-order term $u(1-u)(S-u)$, with a velocity field one derivative smoother than $u$. Littlewood–Paley energy estimates for transport–diffusion equations hold uniformly in $\varepsilon$ in $B^{1+d/p}_{p,1}$ (which embeds in $W^{1,\infty}$), giving a common existence time. The difference $u^\varepsilon-u^0$ satisfies a transport equation forced by $\varepsilon\Delta u^0$; estimating this forcing in a lower norm and interpolating between the uniform bound and the loss of derivatives produces the rates, and the $\varepsilon^{1/2}$ in $L^\infty$ reflects the parabolic smoothing scale $\sqrt{\varepsilon t}$ acting on a datum with a Lipschitz-type singularity.

## Sources

- Yang Cen, Zhaoyang Yin, "Inviscid limit for the hyperbolic Keller–Segel equations in $B_{\infty,1}^{1}$", arXiv:2610.41670 (2026), Theorems 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2610.41670>.
