# Gamma-mixture smoothing distributions of the Dawson–Watanabe diffusion

Let $\alpha$ be a finite non-null measure on a Polish space $\mathbb{Y}$, $\beta > 0$, and $\Gamma^{\beta}_{\alpha}$ the law of a gamma random measure with shape $\alpha$ and rate $\beta$. Let $Z$ be the subcritical Dawson–Watanabe branching diffusion with transition function

$$P_t(z, dz') = \sum_{m\ge0} \mathrm{Po}\bigl(m \mid S_t |z|\bigr) \int_{\mathbb{Y}^m} \Gamma^{\beta+S_t}_{\alpha+\sum_{i\le m}\delta_{y_i}}(dz')\, (z/|z|)^{m}(dy_1,\dots,dy_m), \qquad S_t = \frac{\beta}{e^{\beta t/2}-1}.$$

Given $Z_t = z$, each draw at time $t$ is a Poisson point process with intensity $z$: a $\mathrm{Po}(|z|)$ number of i.i.d. samples from $z/|z|$.

1. **Finite mixture smoothing law.** If the data collected at $0 = t_0 < \dots < t_N$ have $K$ distinct values $y_1,\dots,y_K$, then for each $i$ there are a finite set $\mathcal{M} \subset \mathbb{Z}_+^K$, a constant $b > 0$ and weights $w^b_{\mathbf{m}}$ summing to one with

$$\mathcal{L}(Z_{t_i} \mid \mathbf{Y}_{t_{0:N}}) = \sum_{\mathbf{m}\in\mathcal{M}} w^b_{\mathbf{m}}\, \Gamma^{\beta+b}_{\alpha+\sum_{j=1}^K m_j\delta_{y_j}} .$$

2. **One-step form.** With $c_{i-1}, c_i, c_{i+1}$ draws and total multiplicities $\mathbf{N}_{i-1}, \mathbf{N}_i, \mathbf{N}_{i+1}$ at $t_{i-1}, t_i, t_{i+1}$, the law of $Z_{t_i}$ given these data is a mixture over $\mathbf{0}\le\mathbf{k}_{i-1}\le\mathbf{N}_{i-1}$ and $\mathbf{0}\le\mathbf{k}_{i+1}\le\mathbf{N}_{i+1}$ of $\Gamma^{\beta(\Delta_i,\Delta_{i+1})}_{\alpha+\sum_j(k_{i-1,j}+N_{i,j}+k_{i+1,j})\delta_{y_j}}$, with common rate

$$\beta(\Delta_i,\Delta_{i+1}) = \beta + C^{c_{i-1}}_{\Delta_i} + c_i + C^{c_{i+1}}_{\Delta_{i+1}}, \qquad C^{c}_t = \frac{\beta c}{(\beta+c)e^{\beta t/2} - c}.$$

## Depends on

- [Dirichlet-mixture smoothing distributions of the Fleming–Viot diffusion](dirichlet-mixture-smoothing-distributions-of-the-fleming-viot-diffusion.md)

## Expansion

On a finite partition the signal is a vector of independent Cox–Ingersoll–Ross (continuous-state branching) processes, dual to a death process on $\mathbb{Z}_+^K$ coupled with the deterministic sample-size process $C_t$, which decreases from $c$ to $0$. Data from adjacent times therefore act like $C_{\Delta}$ effective draws together with thinned multiplicities, which shifts both the rate and the shape of the gamma posterior. The rest of the argument matches the Fleming–Viot case.

## Sources

- Filippo Ascolani, Antonio Lijoi and Matteo Ruggiero, "Smoothing distributions for conditional Fleming–Viot and Dawson–Watanabe diffusions", Bernoulli 29 (2023), 1410–1434, <https://doi.org/10.3150/22-BEJ1504>. Numbering follows the arXiv version, arXiv:2204.12738 (2022): Theorem 1.1, Theorem 3.4, Proposition 3.6 and Theorem 4.4, <https://doi.org/10.48550/arXiv.2204.12738>.
