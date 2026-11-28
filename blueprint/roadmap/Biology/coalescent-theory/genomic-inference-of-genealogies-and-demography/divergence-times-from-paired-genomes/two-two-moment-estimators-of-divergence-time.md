# Two-Two (TT) moment estimators of divergence time

In the setting of [sample-configuration probabilities for two gene copies per population](two-two-sample-configuration-probabilities.md), assume in addition a constant ancestral population size $N_A$ (in chromosomes), so that $E[T_{4k}] = 2N_A/(k(k-1))$; with $\theta = \mu N_A$ this gives $\tau_2 = \theta$, $\tau_3 = \theta/3$, $\tau_4 = \theta/6$. Write $T_k = \mu t_k$ and $V_k = \mu\nu_k$. Let $m_{i,j}$ be the observed number of sites in configuration $O_{i,j}$ among $m_{\mathrm{tot}}$ sites.

**Proposition.** The configuration probabilities become

$$p_{1,1} = \tfrac23\alpha_1\alpha_2\theta, \quad p_{2,1} = \tfrac13(2-\alpha_1)\alpha_2\theta, \quad p_{1,0} = 2\alpha_1 T_1 + 2(1-\alpha_1)V_1 + \tfrac13\alpha_1(4-\alpha_2)\theta, \quad p_{2,0} = (1-\alpha_1)(T_1 - V_1) + \tfrac16(6 - 4\alpha_1 - 2\alpha_2 + \alpha_1\alpha_2)\theta,$$

and symmetrically for population 2. Setting $p_{i,j} = m_{i,j}/m_{\mathrm{tot}}$ and solving gives

$$\hat\alpha_1 = \frac{2m_{1,1}}{2m_{2,1} + m_{1,1}}, \qquad \hat\alpha_2 = \frac{2m_{1,1}}{2m_{1,2} + m_{1,1}}, \qquad \hat\theta = \frac{3}{8\,m_{\mathrm{tot}}}\frac{(2m_{2,1} + m_{1,1})(2m_{1,2} + m_{1,1})}{m_{1,1}},$$

$$\hat T_1 = \frac{1}{m_{\mathrm{tot}}}\Big(\frac{m_{1,0}}{2} + m_{2,0} - \frac{(2m_{2,1} + m_{1,1})(6m_{1,2} + m_{1,1})}{8m_{1,1}}\Big), \qquad \hat V_1 = \frac{1}{m_{\mathrm{tot}}}\Big(\frac{m_{1,0} + m_{1,2}}{2} - \frac{m_{1,1}(2m_{2,0} - m_{1,2})}{2m_{2,1} - m_{1,1}}\Big),$$

with $\hat T_2, \hat V_2$ obtained by exchanging the indices. The divergence time in years is $\hat t_k = G\hat T_k/\mu$ for generation time $G$. Because the model is saturated by these equations, the solution is also the maximum composite-likelihood estimate.

## Depends on

- [Sample-configuration probabilities for two gene copies per population](two-two-sample-configuration-probabilities.md)

## Expansion

From $p_{1,1}$ and $p_{2,1}$, $2p_{2,1} + p_{1,1} = \tfrac43\alpha_2\theta$, so $p_{1,1}/(2p_{2,1} + p_{1,1}) \cdot 2 = \alpha_1$; the analogous ratio gives $\alpha_2$ and then $\theta$. Next $\tfrac12 p_{1,0} + p_{2,0} = T_1 + \theta(1 - \alpha_2/3)$, and $(2p_{2,1} + p_{1,1})(6p_{1,2} + p_{1,1})/(8p_{1,1}) = \theta(1 - \alpha_2/3)$, which yields $\hat T_1$; $\hat V_1$ follows from $p_{1,0}$ once $\alpha_1$, $\theta$ and $T_1$ are known, using $1 - \alpha_1 = (2p_{2,1} - p_{1,1})/(2p_{2,1} + p_{1,1})$. Since $m_{1,0}$ appears only in $\hat T_1$ and $\hat V_1$, extra singletons from sequencing error or DNA damage in one sample bias only that branch's estimates. If the ancestral population went through a bottleneck, $\tau_4$ is smaller than $\theta/6$ and the TT estimates are biased; an outgroup-ascertained variant of the method (TTo) estimates the drift parameters without assuming a constant ancestral size.

## Sources

- P. Sjödin, J. McKenna and M. Jakobsson, "Estimating divergence times from DNA sequences", Genetics 217 (2021), iyab008, <https://doi.org/10.1093/genetics/iyab008> (PMC8049563). Section "Assuming a constant ancestral population size (TT)", Equations 3–4.
