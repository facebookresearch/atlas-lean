# Brownian shift limit of fully pushed stochastic fronts

**Setting.** Fix $\alpha\in(0,2)$ and a reaction term $f$ admitting a decreasing travelling wave $m:\mathbb R\to(0,1)$ of speed $\alpha$, $m''+\alpha m'+f(m)=0$, $m(-\infty)=1$, $m(+\infty)=0$, with $m(x)\sim k e^{-x}$ as $x\to\infty$. The motivating example is the diploid selection term
$$f(u)=u(1-u)(2u-1+\alpha),\qquad m(x)=\frac{1}{1+e^x},$$
for an allele $a$ with genotype fitnesses $aa:aA:AA=1+2\alpha s:1+(\alpha-1)s:1$. Let $W$ be a cylindrical Wiener process on $L^2(\mathbb R)$ and $u^N$ the mild solution of the SPDE with Wright–Fisher noise
$$du^N_t=\big(\partial_{xx}u^N_t+f(u^N_t)\big)dt+\sqrt{\tfrac1N\,u^N_t(1-u^N_t)}\,dW(t),$$
started from $u^N_0$ which is $N^{-c}$-close to a shift $m_\eta=m(\cdot-\eta)$ in the weighted norm $\|g\|_{2,\alpha}^2=\int g(x)^2e^{\alpha x}dx$, equals $0$ beyond $(1+c')\log N$ and $1$ below $-N$, and satisfies Hölder and tail bounds.

**Theorem.** Let $\alpha\in(0,3/2)$ (the entire *fully pushed* regime) and $v^N_t(x)=u^N_{Nt}(x+\alpha Nt)$. For every $T>0$ there are real processes $\xi^N$ with
$$\sup_{t\le T}\|v^N_t-m_{\xi^N_t}\|_{2,\alpha}\to0\quad\text{in probability},$$
and $(\xi^N_t-\xi^N_0)_{t\le T}$ converges in distribution in $D([0,T],\mathbb R)$ to $\xi_t=-\mu t+\sigma B_t$, with $B$ a standard Brownian motion,
$$\sigma^2=A_1=\frac{1}{\|m'\|_{2,\alpha}^4}\int_{\mathbb R}m'(x)^2\,m(x)(1-m(x))\,e^{2\alpha x}\,dx,\qquad \mu=\frac\alpha4A_1+\frac12A_2,$$
where $A_2$ is an explicit finite integral involving the fundamental solution of the linearization $\partial_t-\partial_{xx}-\alpha\partial_x-f'(m)$ and $f''(m)$. Both constants diverge as $\alpha\uparrow 3/2$, so the range is optimal for diffusive front fluctuations on time scale $N$.

## Expansion

The deterministic PDE in the moving frame has the one-dimensional invariant manifold $M=\{m_\eta:\eta\in\mathbb R\}$ of shifted waves, which attracts nearby data exponentially fast in $\|\cdot\|_{2,\alpha}$. Following Katzenberger's method for SDEs with a strong drift towards a manifold (in its infinite-dimensional form due to Funaki), one defines the asymptotic phase $\zeta(v)$ of the deterministic flow and applies Itô's formula to $\zeta(v^N_t)$: the first derivative $D\zeta(m)\propto m' e^{\alpha x}/\|m'\|_{2,\alpha}^2$ paired with the noise gives the variance $A_1$, and the Itô correction from $D^2\zeta$ gives the drift. The weight $e^{2\alpha x}$ against $m'^2\sim e^{-2x}$ makes $A_1$ finite exactly when $\alpha<3/2$, the threshold at which the dynamics are no longer dominated by the bulk of the front (semi-pushed waves). The noise near the tip of the front is controlled by a separate analysis of the right interface, using the compact support property.

## Sources

- A. Etheridge, R. Forien, T. Hughes, S. Penington, "Fluctuations for fully pushed stochastic fronts", arXiv:2604.00128 (2026), Section 1.2 (SPDE definition, initial-data assumption and main fluctuation theorem with constants $A_1,A_2$) and Section 2 (finiteness of $A_2$), <https://doi.org/10.48550/arXiv.2604.00128>.
