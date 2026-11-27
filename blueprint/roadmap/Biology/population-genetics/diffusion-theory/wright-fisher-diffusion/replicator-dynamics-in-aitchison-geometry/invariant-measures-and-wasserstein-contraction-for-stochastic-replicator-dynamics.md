# Invariant measures and Wasserstein contraction for stochastic replicator dynamics

**Model.** For a payoff matrix $A \in \mathbb{R}^{n\times n}$, the stochastic replicator equation of Fudenberg and Harris with unit noise intensities is, in Stratonovich form on the open simplex $\Delta$,

$$ dY^i_t = Y^i_t\big((AY_t)_i - Y_t^{\mathsf T}AY_t\big)\,dt + Y^i_t\Big(\circ dB^i_t - \sum_{j=1}^n Y^j_t\circ dB^j_t\Big), \qquad i = 1,\dots,n . $$

In the Aitchison geometry of $\Delta$ (perturbation $\oplus$, inner product $\langle p,q\rangle_A = \frac{1}{2n}\sum_{i,j}\ln\frac{p_i}{p_j}\ln\frac{q_i}{q_j}$, reference measure $\lambda_A$) this is Brownian motion plus the drift field of the deterministic replicator equation $\dot p_i = p_i\big((Ap)_i - p^{\mathsf T}Ap\big)$, a drift that is in general not a gradient.

**Theorem.**
1. (Invariance of the Aitchison measure.) $\lambda_A$ is invariant for the replicator diffusion iff $a_{ij} + a_{ji} - a_{ii} - a_{jj} = 0$ for all $i \ne j$. If moreover $n > 3$, the diffusion is transient: $Y_t \to \partial\Delta$ almost surely.
2. (Wasserstein contraction.) Let $\mu_t, \mu'_t$ be the laws of two solutions, and $W_A$ the Wasserstein distance for the Aitchison metric. Then $W_A(\mu_t,\mu'_t) \le W_A(\mu_0,\mu'_0)$ for all $t \ge 0$ and all initial laws iff

$$ A = -\lambda I + u\otimes\mathbf{1} + \mathbf{1}\otimes v \qquad \text{for some } u, v \in \mathbb{R}^n,\ \lambda \ge 0 . $$

If $\lambda > 0$, additionally $W_\Delta(\mu_t,\mu'_t) \le e^{-\lambda t}W_A(\mu_0,\mu'_0)$ for the Euclidean Wasserstein distance $W_\Delta$. No payoff matrix gives exponential contraction $W_A(\mu_t,\mu'_t) \le e^{-\lambda t}W_A(\mu_0,\mu'_0)$ with $\lambda > 0$.

3. (Deterministic counterpart.) For such $A$ with $\lambda > 0$, any two solutions of the replicator equation satisfy $\|p(t)\ominus q(t)\|_A^2 + 2\lambda\int_0^t\|p(s) - q(s)\|^2\,ds \le \|p\ominus q\|_A^2$ and $\|p(t) - q(t)\| \le e^{-\lambda t}\|p\ominus q\|$, but again no $A$ gives exponential contraction in $\|\cdot\|_A$.

## Depends on

- [Aitchison diffusion: Brownian motion on the simplex as neutral stochastic replicator dynamics](aitchison-diffusion-as-brownian-motion-on-the-simplex.md)
- [Solution of the replicator equation](../../../../population-dynamics/replicator-dynamics/is-solution.md)

## Proof depends on

## Expansion

Since the noise is the intrinsic Brownian motion of the flat Aitchison space, synchronous coupling of two solutions cancels the noise, and $W_A$-contraction reduces to monotonicity of the drift in the Aitchison inner product: $\langle F(p)\ominus F(q), p\ominus q\rangle_A \le 0$. Writing the replicator drift in log-ratio coordinates shows this holds exactly for the stated matrix family. The invariance criterion follows from the stationary Fokker–Planck equation with respect to $\lambda_A$, which requires the drift to be divergence-free in Aitchison coordinates.

## Sources

- Tobias Lehmann, "Darwinian evolution as Brownian motion on the simplex: A geometric perspective on stochastic replicator dynamics", arXiv:2008.05410 (2020), Theorem 16 and Corollary 17 (stationary Fokker–Planck equation, invariance of the Aitchison measure), Corollary 24 and Theorem 25 (contraction estimates), <https://doi.org/10.48550/arXiv.2008.05410>; published in *Annals of Applied Probability* 33(1) (2023) 344–375, <https://doi.org/10.1214/22-AAP1817>. Locators follow arXiv v1.
