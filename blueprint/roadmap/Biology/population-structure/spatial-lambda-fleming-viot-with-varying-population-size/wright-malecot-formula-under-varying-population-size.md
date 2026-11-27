# Wright–Malécot formula under varying population size

**Setting.** In the mSLFV model with limiting population density $n_t$ solving $\partial_t n_t = uV_R\big(\frac{R^2}{d+2}\Delta n_t + r(n_t)n_t\big)$, let $Z_t$ be the Gaussian fluctuation limit and sample two individuals with spatial weights given by probability densities $\psi_1, \psi_2$ on $\mathbb{T}^d$, so the effective sampling densities are $\vartheta_i = n_t \psi_i / \langle n_t, \psi_i\rangle$. The rescaled probability of identity by descent is $N\delta_N^{2-d}\, P^N_t(\psi_1,\psi_2)$, where $P^N_t$ is the probability that the two sampled individuals carry the same type.

**Theorem.** Let $G_{s,t}$ be the fundamental solution of $-\frac{d}{ds} G_{s,t}\psi = A_s^* G_{s,t}\psi$, where $A_s^*$ is the adjoint of the lineage generator

$$A_s \phi = \frac{u V_R R^2}{d+2}\Big(\Delta\phi + 2\,\frac{\nabla n_s}{n_s}\cdot\nabla\phi\Big).$$

Then

$$\mathbb{E}\left[\frac{\langle Z_t\otimes Z_t, \mathbf{1}_{\{k_1=k_2\}}\,\psi_1\otimes\psi_2\rangle}{\langle n_t,\psi_1\rangle\langle n_t,\psi_2\rangle}\right] = u^2 V_R^2 \int_0^t \int_{\mathbb{T}^d} \frac{e^{-2\mu(t-s)}}{n_s(z)+1}\, G_{s,t}\vartheta_1(z)\, G_{s,t}\vartheta_2(z)\, dz\, ds .$$

If the limit $N \to \infty$ can be exchanged with the expectation (stated as a conjecture in the source), this is the limit of $N\delta_N^{2-d}\,P^N_t(\psi_1,\psi_2)$.

## Depends on

- [Central limit theorem for the spatial Λ-Fleming–Viot process with fluctuating population size](central-limit-theorem-for-the-modified-spatial-lambda-fleming-viot-process.md)

## Expansion

Read backwards in time, the formula says each ancestral lineage diffuses with the drift $2\nabla n_s/n_s$, which pulls lineages toward high-density regions; two lineages that meet at $z$ at time $s$ coalesce at rate proportional to $1/(n_s(z)+1)$, and identity requires no mutation on either branch since then, giving the factor $e^{-2\mu(t-s)}$. With constant density the drift vanishes and the classical Wright–Malécot formula is recovered. The identity follows by applying Itô's formula to $Z_t\otimes Z_t$ tested against the diagonal and solving the resulting linear equation with $G_{s,t}$.

## Sources

- Raphaël Forien and Bastian Wiederhold, "Central limit theorems describing isolation by distance under varying population size", ALEA Lat. Am. J. Probab. Math. Stat. 22 (2025), 283, <https://doi.org/10.30757/ALEA.v22-11>. Numbering follows the arXiv version, arXiv:2407.10211 (2024): Conjecture 3.5 and Theorem 3.6 (Section 3, "Wright–Malécot formula"), <https://doi.org/10.48550/arXiv.2407.10211>.
