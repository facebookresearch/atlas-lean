# Steady-state error of the heterogeneous mean-field SIS approximation

**Model.** $M$ agents have susceptibilities $\theta_m \overset{\text{iid}}{\sim} \nu = \mathcal{U}[0,1]$. Each agent is susceptible or infected; infected agents recover at rate $1$. Each infected agent contacts a uniformly chosen agent at rate $1$, and a contacted susceptible agent $m$ becomes infected with probability $\theta_m$; susceptibles are also infected from an external source at rate $\alpha > 0$. Let $X_{\nu_M}(t)$ be the fraction infected, where $\nu_M = \frac1M\sum_m \delta_{\theta_m}$.

**Mean-field limits.** The *quenched* model, for the realized $\nu_M$, is $\dot w_m = (1 - w_m)(\alpha + \theta_m z) - w_m$ with $z = \frac1M\sum_m w_m$, with unique equilibrium

$$
x^*_{\nu_M} = \frac1M\sum_{m=1}^{M}\frac{\alpha + \theta_m x^*_{\nu_M}}{1 + \alpha + \theta_m x^*_{\nu_M}} .
$$

The *annealed* model is $\partial_t w(t,\theta) = (1 - w)(\alpha + \theta z) - w$ with $z = \int_0^1 w(t,\theta)\,d\theta$, with unique equilibrium

$$
x^* = \int_0^1 \frac{\alpha + \theta x^*}{1 + \alpha + \theta x^*}\,d\theta .
$$

**Theorem.** Let $X_{\nu_M}(\infty)$ denote the fraction infected under the stationary law of the $M$-agent Markov chain. Then

$$
\mathbb{E}\bigl[\,|X_{\nu_M}(\infty) - x^*_{\nu_M}|^2 \bigm| \nu_M\bigr] = O(1/M), \qquad
\mathbb{E}\bigl[\,|X_{\nu_M}(\infty) - x^*|^2\bigr] = O(1/M).
$$

More generally, for a heterogeneous mean-field model the quenched bound holds whenever the occupancy dynamics are *stable* ($\int_0^\infty \|x_{\nu_M}(t;\hat w) - x^*_{\nu_M}\|^2 dt \le C_0$ uniformly) and *robust* (first and second derivatives of the occupancy trajectory with respect to a one-transition perturbation $\Delta$ of the initial state have time-integrated size $O(1/M^2)$); the annealed bound additionally needs the equilibrium map to be Lipschitz in a distance $\|\cdot\|_{\mathcal{D}}$ with $\mathbb{E}\|\nu_M - \nu\|^2_{\mathcal{D}} = O(1/M)$. For the SIS model, $\|\rho - \eta\|_{\mathcal{D}} = \sup_{z \in [0,1]}\bigl|\int \frac{\alpha + \theta z}{1 + \alpha + \theta z}(\rho - \eta)(d\theta)\bigr|$.

## Proof sketch

Stein's method compares the generator of the $M$-agent chain with the mean-field vector field through the Stein function $g(\hat w) = -\int_0^\infty \|x(t;\hat w) - x^*\|^2 dt$, whose generator applied gives the squared error up to a Taylor remainder; stationarity makes the expected generator zero, so the error is bounded by second-order terms, each of size $O(1/M)$. In a homogeneous system the state is the occupancy itself and stability alone suffices. With heterogeneity the full agent-level state matters, and a single transition perturbs one agent with its own $\theta_m$, so the occupancy must respond smoothly to such perturbations, which is the robustness condition. The annealed error then splits into the quenched error plus the sampling error of $\nu_M$ propagated through the Lipschitz equilibrium map.

## Related topics

- [SIS epidemic model](../../sis-epidemic-model/README.md)

## Sources

- Lei Ying, "Poster: Steady-State Approximation Error of Heterogeneous Mean-Field Models", in *Proceedings of the Twenty-seventh International Symposium on Theory, Algorithmic Foundations, and Protocol Design for Mobile Networks and Mobile Computing*, ACM, 2026, 629–630, <https://doi.org/10.1145/3842721.3850104>. Preprint version: arXiv:2606.09022 (2026), Theorem 1, Section on the heterogeneous SIS model, Lemmas 1–4, <https://doi.org/10.48550/arXiv.2606.09022>.
