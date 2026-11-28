# Half-time of a reaction driven by flux-limited chemotaxis

**Model (rescaled, in $\mathbb R^2$).** A chemotactic density $\rho_1 \ge 0$ and a stationary attractant-producing density $\rho_2 \ge 0$ satisfy

$$ \partial_t\rho_1 - \Delta\rho_1 + \nabla\cdot\Big(\rho_1\,\frac{\nabla c}{|\nabla c|}\,\Psi(|\nabla c|)\Big) = -\epsilon\rho_1\rho_2, \qquad \partial_t\rho_2 = -\epsilon\rho_1\rho_2, \qquad -\sigma\Delta c = \rho_2, $$

where the *flux limiter* $\Psi:\mathbb R_+\to\mathbb R_+$ is smooth and increasing with $\Psi(z) = \chi z$ for small $z$ and $\Psi(z) = v_0$ (the maximal chemotactic speed) for $z \ge \beta$, $\chi\beta = v_0$. Initially $\rho_2(\cdot,0)$ lies between $2\theta\mathbf 1_{B(0,1-\delta_0)}$ and $2\theta\mathbf 1_{B(0,1)}$, with $\delta_0$ small enough that $\int\rho_2(x,0)\,dx \ge 7\pi\theta/4$ (the source's (1.5): "7πθ/4 ≤ ‖ρ2(·, 0)‖1 ≤ 2πθ, where in the last line we assumed that δ0 is sufficiently small"), while $\rho_1$ has mass $M_0$ in $\{|x| \le L\}$ and only a negligible part of it in $\{|x| \le L/2\}$ (no radial symmetry is assumed). Put $\gamma = \theta\chi/\sigma$ and define the *half-time*

$$ \tau = \sup\Big\{t \ge 0 : \int_{\mathbb R^2}\rho_2(x,t)\,dx \ge \pi\theta\Big\}. $$

**Theorem.** Assume $v_0 \le 1$, $\gamma \gg 1$ (e.g. $\gamma \ge 16$) and $M_0 v_0^2 \gg \theta$, and set $R_0 = \frac{\gamma}{2v_0} - 1$. There is a universal constant $C$ such that

$$ \tau \le \begin{cases} C\Big(\dfrac{1}{v_0^2} + \dfrac{1}{\epsilon v_0^2 M_0}\Big), & L \le v_0^{-1},\\[2mm] C\Big(\dfrac{L}{v_0} + \dfrac{1}{\epsilon v_0^2 M_0}\Big), & v_0^{-1} \le L \le R_0,\\[2mm] C\Big(\dfrac{L^2}{\gamma} + \dfrac{\gamma}{v_0^2} + \dfrac{1}{\epsilon v_0^2 M_0}\Big), & R_0 \le L. \end{cases} $$

By comparison, without chemotaxis the half-time satisfies $\tau_D \gtrsim L^2/\log(M_0\epsilon)$ when $M_0\epsilon \gg 1$ and $\tau_D \gtrsim L^2 e^{C/(M_0\epsilon)}$ when $M_0\epsilon \ll 1$, so chemotaxis shortens the half-time substantially for large $\gamma$, and dramatically in the weak ("risky") reaction regime $M_0\epsilon \ll 1$.

## Expansion

Each term is a transport or reaction time. Far from the target, $|\nabla c| \approx \theta/(\sigma|x|)$ is small, the drift is unsaturated, $\Psi(|\nabla c|) \approx \gamma/|x|$, and moving mass from $|x| \sim L$ to $|x| \sim R_0$ (where the drift reaches the cap) takes time $\sim L^2/\gamma$. Between $R_0$ and $v_0^{-1}$ the drift equals the speed limit $v_0$, giving times $R_0/v_0 \sim \gamma/v_0^2$ or $L/v_0$. At $|x| \sim v_0^{-1}$ drift and diffusion balance, so a mass of order $M_0$ equilibrates over a ball of radius $v_0^{-1}$ in time $v_0^{-2}$, where its density is $\sim M_0 v_0^2$, and reaction with $\rho_2$ then proceeds at rate $\epsilon M_0 v_0^2$. The proof writes the transport part as a Fokker–Planck equation $\partial_t u - \Delta u + \nabla\cdot(u\nabla H) = 0$ with an explicit radial potential $H$ whose drift is dominated by the true chemotactic drift, uses duality with the adjoint equation to propagate lower bounds on the mass in shrinking balls (long-range transport, then transport inside $|x| \sim R_0$), and finally a Harnack-type lower bound on the fundamental solution of a drift–diffusion equation with drift bounded by $v_0$ to show that $\rho_1 \gtrsim v_0^2 M_0$ on most of the unit ball, which forces the decay of $\int\rho_2$. Flux limitation removes the over-concentration of the classical Keller–Segel drift near the target centre, which is what allows non-radial data.

## Sources

- Jing An, Alexander Kiselev, Yao Yao, "Reaction enhancement by flux-limited chemotaxis", arXiv:2508.13704 (2025), Section 1.2 (rescaling, initial conditions, rescaled system), Section 1.3 (half-time, Theorem 1.1 and remarks), Section 3 (construction of $H$), Section 4 (duality lemma, Theorems 4.1–4.2, Corollary 4.2), Section 5 (Harnack-type lemmas). <https://doi.org/10.48550/arXiv.2508.13704>. Published version: Journal of Mathematical Biology 92(4) (2026), article 57, <https://doi.org/10.1007/s00285-026-02383-5>; locators above refer to the arXiv version.
