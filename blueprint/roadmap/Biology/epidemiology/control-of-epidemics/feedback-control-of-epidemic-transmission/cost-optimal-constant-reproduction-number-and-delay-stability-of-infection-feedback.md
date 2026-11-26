# Cost-optimal constant reproduction number and delay stability of infection-rate feedback

**Setting.** A population of size $N$ is stratified by activity level $r$ (number of contacts) and fragility $p$, with fractions $f_{r,p}$. Infection follows

$$\dot S_{r,p} = -\frac{\sigma}{\rho(t)}\,\widetilde I(t)\,\frac{rS_{r,p}}{\sum_{r',p'}r'Nf_{r',p'}} + \dots, \qquad \dot I_{r,p} = \frac{\sigma}{\rho(t)}\,\widetilde I(t)\,\frac{rS_{r,p}}{\sum_{r',p'}r'Nf_{r',p'}} - \gamma I_{r,p}, \qquad \widetilde I = \sum_{r,p} rI_{r,p},$$

with downstream hospital and ICU compartments; $\rho(t) \ge 1$ is a restriction factor (social distancing divides transmission by $\rho$) with economic cost rate $\mathfrak{C}(\rho)$. While susceptibles are approximately constant, $S_{r,p} \approx Nf_{r,p}$, the activity-weighted infected count obeys

$$\dot{\widetilde I}(t) = \gamma\big(\mathcal{R}^\rho(t) - 1\big)\widetilde I(t), \qquad \mathcal{R}^\rho(t) = \frac{\mathcal{R}_0}{\rho(t)}, \qquad \mathcal{R}_0 = \frac{\sigma}{\gamma}\frac{\mathbb{E}[r^2]}{\mathbb{E}[r]}.$$

**Proposition (cost-optimal restrictions).** Let $\mathfrak{C}$ be increasing and convex on $[1,\infty)$. Among all restriction paths on $[0,t_{\max}]$ reaching a prescribed level $\widetilde I(t_{\max}) = \widetilde I^\star$, total cost $\int_0^{t_{\max}}\mathfrak{C}(\rho(t))\,dt$ is minimized by keeping the effective reproduction number constant,

$$\mathcal{R}^\rho(t) \equiv 1 + \frac{1}{\gamma t_{\max}}\log\frac{\widetilde I^\star}{\widetilde I(0)}.$$

In particular, among strategies that never let $\widetilde I$ exceed its initial value, keeping $\mathcal{R}^\rho \equiv 1$ is cost-optimal.

**Theorem (delayed feedback on new infections).** Suppose restrictions are set by feedback on the observed unrestricted new-infection rate $\lambda_U$ relative to a target $\lambda_C$ (with $S_{r,p} \approx Nf_{r,p}$):

1. *Constant delay $d$:* $\rho(t) = \max\{1, \lambda_U(t-d)/\lambda_C\}$. The controlled system is locally stable if $\gamma d < \pi/2$ and unstable otherwise.
2. *Distributed delay with density $\mathfrak{f}_d$ and Laplace transform $\mathfrak{F}_d$:* $\rho(t) = \max\{1, \int\mathfrak{f}_d(\tau)\lambda_U(t-\tau)\,d\tau/\lambda_C\}$. If every root of $z + \gamma\mathfrak{F}_d(z) = 0$ has negative real part, the system is locally stable. For an exponential delay $\mathfrak{f}_d(\tau) = \delta e^{-\delta\tau}$ it is always stable; for a shifted exponential $\mathfrak{f}_d(\tau) = \delta e^{-\delta(\tau-d)}\mathbf{1}_{\tau\ge d}$ there is a critical delay $d^* = f(\delta)/\gamma$, increasing from $1/\gamma$ to $\pi/(2\gamma)$ as $\delta$ goes from $0$ to $\infty$, with stability exactly for $d < d^*$.

**Hospital-based feedback.** Controlling instead on hospital and ICU occupancies $H, T$ via $\rho = \max(\rho_H(H), \rho_T(T))$ yields stationary occupancies $H^* = \frac{\gamma}{\phi}\widetilde I^*\frac{\mathbb{E}[r\,p^{IH}]}{\mathbb{E}[r^2]}$, $T^* = \frac{\gamma}{\tau}\widetilde I^*\frac{\mathbb{E}[r\,p^{IH}p^{HT}]}{\mathbb{E}[r^2]}$, which are locally stable if $\rho_H(H^*) > \rho_T(T^*)$, or if $\rho_T(T^*) \ge \rho_H(H^*)$ and $\phi + \tau \ge T^*\rho_T'(T^*)\gamma/\mathcal{R}_0$.

## Expansion

Solving the linear equation gives $\widetilde I(t_{\max}) = \widetilde I(0)\exp\big(\gamma\int_0^{t_{\max}}(\mathcal{R}^\rho - 1)\big)$, so the target fixes the time average of $\mathcal{R}^\rho$. Since $\rho = \mathcal{R}_0/\mathcal{R}^\rho$, the cost is $\int\chi(\mathcal{R}^\rho)$ with $\chi = \mathfrak{C}\circ(\mathcal{R}_0/\cdot)$ convex, and Jensen's inequality makes the constant path optimal. Linearizing the delayed feedback around the equilibrium where $\lambda_U = \lambda_C\rho$ gives the characteristic equation $z + \gamma e^{-zd} = 0$ (or $z + \gamma\mathfrak{F}_d(z) = 0$), whose roots cross the imaginary axis when $\gamma d = \pi/2$; infection-rate data are noisy and reported late, which is why delay-induced oscillations are a practical risk, whereas hospital data are cleaner but lag further behind infections.

## Sources

- Franco Galante, Chiara Ravazzi, Michele Garetto and Emilio Leonardi, "Planning interventions in a controlled pandemic: the COVID-19 case", arXiv:2207.03280 (2022), Section 2 (base model), Section 4 (cost-minimizing proposition and corollary, stability theorems with constant and distributed delay, exponential and shifted-exponential corollaries) and Section 5 (stationary solutions and stability of hospital-based control), <https://doi.org/10.48550/arXiv.2207.03280>. Published version: IEEE Transactions on Network Science and Engineering 11 (2024) 2314–2331, <https://doi.org/10.1109/tnse.2023.3343807>.
