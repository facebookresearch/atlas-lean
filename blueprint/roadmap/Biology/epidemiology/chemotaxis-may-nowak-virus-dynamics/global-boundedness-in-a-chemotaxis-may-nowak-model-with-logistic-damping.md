# Global boundedness in a chemotaxis May–Nowak model with logistic damping

Let $\Omega\subset\mathbb{R}^n$, $n\ge2$, be bounded and smooth, with homogeneous Neumann conditions, and consider
$$\begin{cases}
u_t=\Delta u-\chi\nabla\cdot(u\nabla v)+\kappa-u-uw-\mu\,\dfrac{u^{1+\alpha}}{\ln^k(u+e)},\\[1mm]
\gamma v_t=\Delta v-v+uw,\\[1mm]
w_t=\Delta w-w+v,
\end{cases}$$
where $u$ are uninfected cells, $v$ infected cells and $w$ free virus; $\chi\in\mathbb{R}$, $\mu>0$, $\alpha>0$, $k\in[0,1)$, $\gamma\in\{0,1\}$, and the source $\kappa\in C^1(\bar\Omega\times[0,\infty))$ is nonnegative with $\|\kappa\|_{L^\infty}\le\kappa_*$. The chemotactic term (attractive or repulsive, depending on the sign of $\chi$) couples cell motion to infected-cell density.

**Theorem (parabolic case, $\gamma=1$).** For suitably regular nonnegative initial data, the system has a unique global classical solution, positive in $\bar\Omega\times(0,\infty)$, with

$$\sup_{t>0}\Bigl(\|u(t)\|_{L^\infty}+\|v(t)\|_{W^{1,\infty}}+\|w(t)\|_{L^\infty}\Bigr)<\infty,$$

in each of the cases
- (A) $n=2$, $k\in[0,1)$, $\alpha=1$, $\mu>0$ (sub-logistic damping $u^2/\ln^k(u+e)$ suffices in the plane);
- (B) $3\le n\le5$, $k=0$, $\alpha=1$, $\mu>\mu_0$ for some $\mu_0>0$;
- (C) $n\ge6$, $k=0$, $\alpha>\frac{n-2}{4}$, $\mu>0$.

**Theorem (parabolic–elliptic case, $\gamma=0$).** If $k=0$, $\alpha>\frac{n+2}{2}$ and $\mu>0$, there is a unique global classical solution, positive and uniformly bounded.

## Expansion

The infection term $-uw$ is a loss for $u$, so the danger is chemotactic aggregation driven by $\nabla v$. The proof derives an $L^p$ estimate for $u$ with $p>n/2$ from a functional combining $\int u^p$ with gradient norms of $v$ and $w$; the cross term $\chi\int u^{p-1}\nabla u\cdot\nabla v$ is absorbed by the damping $\mu\int u^{p+\alpha}/\ln^k(u+e)$ after Gagliardo–Nirenberg and maximal Sobolev regularity estimates for the $v$- and $w$-equations. In two dimensions the weaker growth of the planar regularity estimates tolerates the logarithmic loss in the damping; in higher dimensions the damping exponent must outgrow the dimension-dependent regularity loss of the cascade $u\to v\to w$, which gives the thresholds on $\alpha$ and $\mu$. Boundedness then follows by Moser iteration.

## Sources

- M. Le, "Global boundedness in a Chemotaxis-May-Nowak model for virus dynamics with logistic damping", arXiv:2609.29134 (2026), Section 1 (model and hypothesis on $\kappa$), Theorems 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2609.29134>.
