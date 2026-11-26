# Unique quasi-stationary distribution and fixation tail of the stochastic FKPP on the circle

**Model.** Let $\mathbb{S}\simeq[0,1)$ be the circle of circumference $1$ and $\dot W$ space-time white noise. For constants $\alpha,\gamma>0$ and $\beta\ge 0$, the stochastic FKPP equation

$$\partial_t u=\tfrac{\alpha}{2}\Delta u+\beta\,u(1-u)+\sqrt{\gamma\,u(1-u)}\,\dot W,\qquad (t,x)\in(0,\infty)\times\mathbb{S},$$

(interpreted as a mild solution) describes the local frequency $u(t,x)\in[0,1]$ of a favoured type in a spatial population with migration rate $\alpha$, selection $\beta$ and genetic drift $\gamma$. Its two absorbing states are the constants $\mathbf{0}$ and $\mathbf{1}$; let $\tau_{\mathrm{fix}}$ be the hitting time of $\{\mathbf 0,\mathbf 1\}$ and $\mathcal{C}_*=C(\mathbb{S};[0,1])\setminus\{\mathbf 0,\mathbf 1\}$.

**Statement.**
1. *(Unique QSD.)* There is a unique quasi-stationary distribution $\pi$ on $\mathcal{C}_*$, and for every initial law $\mu$,

$$\mathbb{P}_\mu\big(u_t\in\cdot\mid\tau_{\mathrm{fix}}>t\big)\to\pi\qquad(t\to\infty).$$

2. *(Fixation tail.)* There are $\lambda\in(0,1)$, equal to the eigenvalue of $\pi$ ($\mathbb{P}_\pi(\tau_{\mathrm{fix}}>t)=\lambda^t$), and a unique positive bounded continuous right eigenfunction $h$ of the killed semigroup, such that

$$\lambda^{-t}\,\mathbb{P}_\mu(\tau_{\mathrm{fix}}>t)\to\frac{\mu(h)}{\pi(h)}\qquad(t\to\infty).$$

3. *(Neutral case, $\beta=0$.)* Let $\theta_*\in(0,\pi/2)$ solve $\gamma/\alpha=4\theta\tan\theta$. Then

$$\lambda=e^{-4\alpha\theta_*^2},$$

and the QSD of the two-particle killed coalescing Brownian dual has density $\rho^0(x,y)=\frac{\theta_*}{\sin\theta_*}\cos\!\big(2\theta_*(\tfrac12-d_{\mathbb{S}}(x,y))\big)$ on $\mathbb{S}\times\mathbb{S}$. Under $\pi$, for a closed $F\subsetneq\mathbb{S}$, the probability that $u$ is not fixed on $F$ is $\mathbf{E}_F[e^{4\alpha\theta_*^2\tau_1}]/\mathbf{E}_{\mathbb{S}}[e^{4\alpha\theta_*^2\tau_1}]\in(0,1)$, where $\tau_1$ is the time at which a coalescing Brownian system started from $F$ is reduced to two particles at one point.

## Expansion

The equation is moment dual to a system of branching-coalescing Brownian motions, and the killed version used here is a two-type system (green and red particles) killed when one particle of each colour meets: $\mathbb{E}_f[\mathcal{E}^z(u_t);\tau_{\mathrm{fix}}>t]=\mathbf{E}_z[\mathcal{E}^{Z_t}(f);\tau_\partial>t]$. The dual is a finite-dimensional killed process, for which a Champagnat-Villemonais type argument gives a unique QSD $\varphi$ and right eigenfunction $\phi$ with exponential convergence. Duality transfers the pair: $\phi(z)=\int\mathcal{E}^z(f)\,\pi(df)$, and tightness of the conditioned laws of $u_t$ gives existence of $\pi$, while the duality functions separate points, giving uniqueness. When $\beta=0$, the green-red separation is a Brownian motion on the circle killed at $0$ at a rate set by the drift-to-migration ratio, and the principal Dirichlet-Robin eigenvalue is $4\alpha\theta_*^2$ with $\theta_*$ the root of the transcendental equation.

## Sources

- Wai-Tong Louis Fan, Oliver Tough, "Quasi-stationary behavior of the stochastic FKPP equation on the circle", arXiv:2309.10998 (2023), Theorems 2.1, 2.3, 3.5, 3.7, 4.1 and 4.6, Proposition 3.4, <https://doi.org/10.48550/arXiv.2309.10998>.
