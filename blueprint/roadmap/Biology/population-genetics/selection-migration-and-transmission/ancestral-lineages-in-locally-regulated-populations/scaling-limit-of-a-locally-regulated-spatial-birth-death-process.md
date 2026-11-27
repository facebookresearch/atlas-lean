# Scaling limit of a locally regulated spatial birth–death process

**Model.** Individuals live in $\mathbb{R}^d$; the state is a counting measure $X$, and $\eta^N_t = X(\theta t)/N$ puts mass $1/N$ on each individual. Local density is measured by convolution with smooth nonnegative integrable kernels $\rho_\gamma,\rho_r,\rho_F$; write $\gamma(x,\eta)=\gamma(x,\rho_\gamma*\eta(x))$, and similarly $r(x,\eta)$, $F(x,\eta)$. In the unscaled process:

- an individual at $x$ produces one juvenile at rate $\gamma(x,\eta)$;
- the juvenile is displaced by a Gaussian with mean $\vec b(x)/\theta$ and covariance $\mathbf{C}(x)/\theta$ (density $q_\theta(x,\cdot)$), and establishes at its new location $y$ with probability $r(y,\eta)$, otherwise it dies at once;
- an individual at $x$ dies at rate $\mu_\theta(x,\eta)=r(x,\eta)\gamma(x,\eta)-\theta^{-1}F(x,\eta)\ge 0$.

So $F$ is (up to the nonlocal effect of establishment being judged at the offspring's location) the net per-capita growth rate, scaled by $\theta$. The dispersal generator is

$$\mathcal{B}f(x)=\tfrac12\sum_{i,j}\mathbf{C}_{ij}(x)\,\partial_{x_i}\partial_{x_j}f(x)+\sum_i \vec b_i(x)\,\partial_{x_i}f(x).$$

**Theorem.** Assume $\vec b,\mathbf{C}$ are bounded and Hölder, $\mathcal{B}$ is uniformly strictly elliptic, $F$ is locally Lipschitz in $m$, bounded above, and satisfies $\sup_x\sup_{k\le m}|F(x,k)|<\infty$ for each fixed $m$, $r,\gamma$ have bounded first and second derivatives, $\gamma$ is bounded, and the regularity bound $\left|\gamma(x,\eta)\,\theta\int (r(y,\eta)f(y)-r(x,\eta)f(x))\,q_\theta(x,dy)\right|\le C_f(1+|f(x)|)$ holds for $f\in C^2_b(\mathbb{R}^d)$. Let $N\to\infty$ and $\theta=\theta(N)\to\infty$ with $\theta/N\to\alpha\in[0,\infty)$, the kernels fixed, and let the initial measures $\eta^N_0$ be tight with $\langle f_0,\eta^N_0\rangle$ uniformly bounded for some nonnegative $f_0\in C(\mathbb{R}^d)$ with bounded first and second derivatives and $f_0(x)\to\infty$ as $|x|\to\infty$. Then $(\eta^N_t)_{t\ge0}$ is tight in $\mathcal{D}_{[0,\infty)}(\mathcal{M}_F(\mathbb{R}^d))$, and every limit point $\eta$ satisfies: for each $f\in C_b^\infty(\mathbb{R}^d)$,

$$M_t(f)=\langle f,\eta_t\rangle-\langle f,\eta_0\rangle-\int_0^t\big\langle \gamma(x,\eta_s)\,\mathcal{B}\big(f(\cdot)\,r(\cdot,\eta_s)\big)(x)+f(x)F(x,\eta_s),\ \eta_s(dx)\big\rangle\,ds$$

is a martingale with

$$\langle M(f)\rangle_t=\alpha\int_0^t\big\langle 2\gamma(x,\eta_s)\,r(x,\eta_s)\,f(x)^2,\ \eta_s(dx)\big\rangle\,ds.$$

If $\alpha>0$ the limit is an interacting superprocess; if $\alpha=0$ it is deterministic, a weak solution of the nonlocal reaction–diffusion equation

$$\partial_t\varphi=r\,\mathcal{B}^*(\gamma\varphi)+\varphi F .$$

When the martingale problem has a unique solution, the whole sequence converges to it.

A companion local limit holds: with $r\equiv\gamma\equiv1$, $\mathcal{B}=\Delta/2$, $F(x,m)=F(m)$ a polynomial bounded above on $m\ge0$, and $\rho_F$ a Gaussian of variance $\epsilon^2$, if $N,\theta\to\infty$ and $\epsilon\to0$ with $1/(\theta\epsilon^2)+\theta/(N\epsilon^d)\to0$ (and suitable moment bounds on the smoothed initial data), then $\rho_F^\epsilon*\eta^N_t(x)\,dx$ converges weakly to a measure with density solving $\partial_t\varphi=\tfrac12\Delta\varphi+\varphi F(\varphi)$, e.g. the Fisher–KPP equation when $F(m)=1-m$.

## Expansion

The generator of $\langle f,\eta^N\rangle$ has a drift term $\theta\gamma\int(r(y)f(y)-r(x)f(x))q_\theta(x,dy)+F f$; since $q_\theta$ has mean and covariance of order $1/\theta$, the first term converges to $\gamma\,\mathcal{B}(rf)$. Each birth or death changes $\langle f,\eta\rangle$ by $\pm f/N$ at total rate of order $\theta N$, so the quadratic variation is of order $\theta/N\to\alpha$, with both births and deaths contributing $r\gamma f^2$ to leading order. The ratio $\alpha$ therefore decides between demographic noise surviving (superprocess) and a law of large numbers (PDE). Tightness uses compact containment from the Lyapunov function $f_0$ and the Aldous–Rebolledo criterion. Note that $\mathcal{B}(fr)$ rather than $r\mathcal{B}f$ appears: establishment is judged at the offspring's site, which is why the regularity condition on $r$ is needed for the net growth to stay of order $1/\theta$.

## Sources

- Alison M. Etheridge, Thomas G. Kurtz, Ian Letter, Peter L. Ralph and Terence Tsui Ho Lung, "Looking forwards and backwards: Dynamics and genealogies of locally regulated populations", Electron. J. Probab. 29 (2024), 1–85, <https://doi.org/10.1214/24-EJP1075>. Numbering follows the arXiv version, arXiv:2305.14488 (2023): Assumptions 2.8, Theorem 2.10, Corollary 2.11, Definition 2.12 and Theorem 2.21, <https://doi.org/10.48550/arXiv.2305.14488>.
