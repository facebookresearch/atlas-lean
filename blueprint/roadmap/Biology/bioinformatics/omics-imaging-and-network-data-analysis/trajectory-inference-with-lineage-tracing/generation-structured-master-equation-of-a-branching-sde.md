# Generation-structured master equation of a branching SDE

**Setting.** Cell states $X_t \in \mathcal X \subseteq \mathbb{R}^g$ (gene expression) move by the
gradient SDE

$$dX_t = -\nabla\Psi(t, X_t)\,dt + \sqrt{\tau}\,dB_t$$

(diffusivity $\tau$; $\nabla\Psi$ globally Lipschitz), whose law $p_t$ solves the Fokker–Planck equation
$\partial_t p = \operatorname{div}(p\nabla\Psi) + \frac{\tau}{2}\Delta p =: L^*_{\Psi,\tau} p$. In the
**branching SDE**, each cell independently divides into two cells at its current position at rate
$b(t,x)$ and dies at rate $d(t,x)$, with $\|b + d\|_\infty < \infty$, starting from an initial
probability measure $\mu_0$. Each cell carries its **generation number** $m$, the number of divisions
in its ancestry, and $Z_t(m) = \sum_{(m,x)\in N(t)} \delta_x$ is the empirical measure of the
generation-$m$ cells at time $t$; its intensity $\rho_t(m) = \mathbb{E}[Z_t(m)]$ is defined by
$\langle\theta, \rho_t(m)\rangle = \mathbb{E}\langle\theta, Z_t(m)\rangle$.

**Proposition 5.** The intensities $\{\rho(m)\}_{m\in\mathbb N}$ solve, in the weak sense, the system

$$\partial_t \rho(m) = L^*_{\Psi,\tau}\rho(m) + 2b\,\rho(m-1) - (b + d)\,\rho(m), \qquad m \ge 0,$$

with $\rho(-1) = 0$ and initial condition $\rho_0(m) = \mu_0\,\mathbf 1_{m=0}$. Summing over $m$ recovers
the equation $\partial_t\rho = L^*_{\Psi,\tau}\rho + (b - d)\rho$ for the total intensity of the branching
SDE.

## Expansion

Between branching events every cell follows the SDE, which produces the transport–diffusion term.
When a generation-$m$ cell's exponential clock rings it either dies or is replaced by two cells of
generation $m+1$ at the same position, giving the loss term $-(b+d)\rho(m)$ and the gain term
$2b\rho(m-1)$. The proof uses the Markov and branching properties: the generating functional
$u(t,m,x) = \mathbb E_{(m,x)}\prod_{(M,X)\in N(t)} u_0(M,X)$ satisfies a backward equation with generator
$L_{\Psi,\tau}u_0(m) + b\,u_0(m+1)^2 + d - (b+d)u_0(m)$, and linearizing around $u_0 = 1 - \varepsilon\theta$
yields the weak form of the forward system.

## Sources

- E. Ventre, A. Forrow, N. Gadhiwala, P. Chakraborty, O. Angel, G. Schiebinger, "Trajectory inference for a branching SDE model of cell differentiation via lineage tracing", Journal of Mathematical Biology 92(5) (2026) 68, <https://doi.org/10.1007/s00285-026-02375-5> (PMC13090286). Section 2 (model, Markov and branching properties, Definition 2, Assumptions 3–4), Section 3.1, Eqs. (9)–(12), Proposition 5 and its proof.
