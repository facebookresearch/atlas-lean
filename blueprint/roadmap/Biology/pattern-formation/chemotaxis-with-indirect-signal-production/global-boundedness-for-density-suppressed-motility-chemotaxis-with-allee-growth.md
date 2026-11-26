# Global boundedness for density-suppressed motility chemotaxis with indirect signal production and a strong Allee effect

Let $\Omega\subset\mathbb R^d$, $d\ge2$, be a bounded domain with smooth boundary, and consider the chemotaxis–growth system with homogeneous Neumann boundary conditions
$$\begin{aligned}
u_t&=\Delta(\gamma(v)u)+\mu u(1-u^\theta)(u-A),\\
v_t&=\Delta v-v+w^\beta,\\
w_t&=-\delta w+u,
\end{aligned}\qquad x\in\Omega,\ t>0,$$
where $u$ is the cell density, $w$ an intermediate (non-diffusing) signal-producing species, $v$ the chemical signal, $\mu,\beta,\delta>0$, $\theta\ge1$ and the Allee threshold $A\in(0,1)$. Initial data satisfy $u_0\in C^0(\overline\Omega)$, $v_0,w_0\in C^1(\overline\Omega)$, $u_0,v_0,w_0\ge0$, $u_0\not\equiv0$. The motility satisfies

- **(H1)** $\gamma\in C^3([0,\infty))$, $\gamma>0$, $\gamma'<0$ on $[0,\infty)$ and $\gamma(v)\to0$ as $v\to\infty$;
- **(H2)** $\lim_{v\to\infty}\gamma'(v)/\gamma(v)$ exists.

**Theorem.**

1. Under (H1), if $\beta<\dfrac{2(\theta+2)}{d}$, the problem has a globally bounded classical solution: there is $C>0$ independent of $t$ with
$$\|u(\cdot,t)\|_{L^\infty(\Omega)}+\|v(\cdot,t)\|_{W^{1,\infty}(\Omega)}+\|w(\cdot,t)\|_{L^\infty(\Omega)}\le C\qquad(t>0).$$
2. Under (H1) and (H2), the same conclusion holds for the larger range $\beta<\dfrac{d(\theta+1)+2(\theta+2)}{2d}$, provided $\theta>\dfrac{4-d}{d-2}$.

Local classical solutions with the stated Hölder regularity are unique.

## Expansion

Writing $\Delta(\gamma(v)u)=\nabla\cdot(\gamma(v)\nabla u+u\gamma'(v)\nabla v)$ shows that density-suppressed motility is a Keller–Segel cross-diffusion with sensitivity $-\gamma'(v)\ge0$, degenerate as $v\to\infty$. The indirect production $u\to w\to v$ smooths the signal: $w(t)=e^{-\delta t}w_0+\int_0^te^{-\delta(t-s)}u(s)\,ds$, so $L^p$ control of $u$ transfers to $w$ and then, by parabolic regularity, to $v$. The $\theta$-logistic term $-\mu u^{\theta+2}$ (dominant at large $u$) provides superlinear damping in the energy estimate for $\int u^p$; the condition on $\beta$ balances the growth of the source $w^\beta$ against this damping via Gagliardo–Nirenberg and Young inequalities. A Moser iteration then upgrades $L^p$ bounds to $L^\infty$, and the extensibility criterion yields global existence. Hypothesis (H2) gives a sharper comparison for $\gamma(v)$ at large $v$, which enlarges the admissible range of $\beta$.

## Sources

- Om Tripathi, Sourav Kumar Sasmal, Manil T. Mohan, "Global existence and uniqueness of solutions in a chemotaxis system with density-suppressed motility, a $θ-$logistic source, and indirect signal production under a strong Allee effect", arXiv:2609.03128 (2026), Section 1 (hypotheses (H1)–(H2)), Theorems 1.1–1.2, Theorems 3.1–3.2 (local existence and uniqueness), <https://doi.org/10.48550/arXiv.2609.03128>.
