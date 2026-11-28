# Invariant measures and Wasserstein contraction for stochastic replicator dynamics

**Model.** For a payoff matrix $A \in \mathbb{R}^{n\times n}$, the stochastic replicator equation of Fudenberg and Harris with unit noise intensities is, in Stratonovich form on the open simplex $\Delta$,

$$ dY^i_t = Y^i_t\big((AY_t)_i - Y_t^{\mathsf T}AY_t\big)\,dt + Y^i_t\Big(\circ dB^i_t - \sum_{j=1}^n Y^j_t\circ dB^j_t\Big), \qquad i = 1,\dots,n . $$

In the Aitchison geometry of $\Delta$ (perturbation $\oplus$, inner product $\langle p,q\rangle_A = \frac{1}{2n}\sum_{i,j}\ln\frac{p_i}{p_j}\ln\frac{q_i}{q_j}$, reference measure $\lambda_A$) this is Brownian motion plus the drift field of the deterministic replicator equation $\dot p_i = p_i\big((Ap)_i - p^{\mathsf T}Ap\big)$, a drift that is in general not a gradient.

**Theorem.**
1. (Invariance of the Aitchison measure.) For the replicator diffusion with noise intensities $\sigma_i = \sqrt2$ (the noise terms of the display above multiplied by $\sqrt2$), $\lambda_A$ is invariant iff $a_{ij} + a_{ji} - a_{ii} - a_{jj} = 0$ for all $i \ne j$. If moreover $n > 3$, the diffusion is transient: $Y_t \to \partial\Delta$ almost surely. This item uses the source's noise convention: Theorem 16 and Corollary 17 sit in its Section 5.1, where, "Mainly for notational convenience, and in this subsection only", the noise of the Fudenberg–Harris model is taken with $\sigma_i = \sqrt2$; items 2 and 3 use the unit-noise equation above, as the source's Section 5.2 does.
2. (Wasserstein contraction.) Let $\mu_t, \mu'_t$ be the laws of two solutions, and $W_A$ the Wasserstein distance for the Aitchison metric. Then $W_A(\mu_t,\mu'_t) \le W_A(\mu_0,\mu'_0)$ for all $t \ge 0$ and all initial laws iff

$$ A = -\lambda I + u\otimes\mathbf{1} + \mathbf{1}\otimes v \qquad \text{for some } u, v \in \mathbb{R}^n,\ \lambda \ge 0 . $$

If $\lambda > 0$, additionally, with $W_\Delta$ the quadratic Wasserstein distance for the Euclidean metric of $\Delta$,

$$W_A(\mu_t,\mu'_t)^2 + 2\lambda\int_0^t W_\Delta(\mu_s,\mu'_s)^2\,ds \le W_A(\mu_0,\mu'_0)^2, \qquad t \ge 0 .$$

No payoff matrix gives exponential contraction $W_A(\mu_t,\mu'_t) \le e^{-\lambda t}W_A(\mu_0,\mu'_0)$ with $\lambda > 0$.

3. (Deterministic counterpart.) For such $A$ with $\lambda > 0$, any two solutions of the replicator equation satisfy $\|p(t)\ominus q(t)\|_A^2 + 2\lambda\int_0^t\|p(s) - q(s)\|^2\,ds \le \|p\ominus q\|_A^2$, but again no $A$ gives exponential contraction in $\|\cdot\|_A$.

*Correction to the source.* The source also claims $\|p(t) - q(t)\| \le e^{-\lambda t}\|p\ominus q\|$ (Corollary 24, printed with no subscript on the right-hand norm) and $W_\Delta(\mu_t,\mu'_t) \le e^{-\lambda t}W_A(\mu_0,\mu'_0)$ (Theorem 25, (104)). Both are false, and both proofs apply Grönwall's inequality to $u(t) \le C - 2\lambda\int_0^t u(s)\,ds$, which does not imply $u(t) \le Ce^{-2\lambda t}$. They are omitted above. In log-ratio coordinates the drift is $-\lambda$ times the centred softmax map, whose derivative at the barycentre is $\frac{\lambda}{n}$ times the identity on centred vectors, so nearby solutions approach each other only at rate about $\lambda/n$. Example: $n = 3$, $A = -I$ ($\lambda = 1$, $u = v = 0$), $p = (0.98, 0.01, 0.01)$, $q = (\tfrac13,\tfrac13,\tfrac13)$. Then $\|p\ominus q\|_A \approx 3.744$ and the Euclidean norm of $p\ominus q$ is about $0.980$, so the claimed bound at $t = 7$ is $e^{-7}\cdot 3.744 \approx 0.0034$ under the Aitchison reading and about $0.0009$ under the Euclidean one, but numerical integration gives $\|p(7) - q(7)\| \approx 0.137$. For the diffusions started at $\delta_p$ and $\delta_q$, a Monte Carlo estimate (4000 synchronously coupled paths) gives $|\mathbb E Y^1_7 - \mathbb E Y'^1_7| \approx 0.124 \pm 0.001$, a lower bound for $W_\Delta(\mu_7,\mu'_7)$ that is again far above $e^{-7}W_A(\delta_p,\delta_q) \approx 0.0034$. The integral estimates stated above are what the source's differential inequalities $\frac{d}{dt}\|Y_t\ominus Y'_t\|_A^2 \le -2\lambda\|Y_t - Y'_t\|^2$ (its (109), and the deterministic analogue) give, after optimizing over the initial coupling.

## Depends on

- [Aitchison diffusion: Brownian motion on the simplex as neutral stochastic replicator dynamics](aitchison-diffusion-as-brownian-motion-on-the-simplex.md)
- [Solution of the replicator equation](../../../../population-dynamics/replicator-dynamics/is-solution.md)

## Proof depends on

## Expansion

Since the noise is the intrinsic Brownian motion of the flat Aitchison space, synchronous coupling of two solutions cancels the noise, and $W_A$-contraction reduces to monotonicity of the drift in the Aitchison inner product: $\langle F(p)\ominus F(q), p\ominus q\rangle_A \le 0$. Writing the replicator drift in log-ratio coordinates shows this holds exactly for the stated matrix family; for $\lambda > 0$ the drift is $-\lambda$ times the gradient of the convex, $1$-smooth log-sum-exp function (plus a constant), and its co-coercivity gives the $-2\lambda\|p - q\|^2$ dissipation behind the integral estimates. The invariance criterion follows from the stationary Fokker–Planck equation with respect to $\lambda_A$, which requires the drift to be divergence-free in Aitchison coordinates.

## Sources

- Tobias Lehmann, "Darwinian evolution as Brownian motion on the simplex: A geometric perspective on stochastic replicator dynamics", arXiv:2008.05410 (2020), Theorem 16 and Corollary 17 (stationary Fokker–Planck equation, invariance of the Aitchison measure), Corollary 24 and Theorem 25 (contraction estimates), <https://doi.org/10.48550/arXiv.2008.05410>; published in *Annals of Applied Probability* 33(1) (2023) 344–375, <https://doi.org/10.1214/22-AAP1817>. Locators follow arXiv v1.
