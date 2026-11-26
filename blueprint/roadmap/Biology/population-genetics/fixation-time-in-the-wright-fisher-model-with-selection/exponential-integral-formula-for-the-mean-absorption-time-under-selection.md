# Exponential-integral formula for the mean absorption time under selection

**Setting.** In a haploid Wright–Fisher population of size $N$ with two alleles, allele $A$ has selective advantage $s$ and the next generation is binomial with the selection-weighted frequency. Let $p$ be the initial frequency of $A$ and $\alpha = 2sN$ the scaled selection coefficient. In the diffusion approximation, the fixation probability $u(p)$ and the mean time $m(p)$ (in generations) until the allele is either lost or fixed solve
$$u'' + \alpha u' = 0, \quad u(0) = 0,\ u(1) = 1; \qquad m''(p) + \alpha\,m'(p) + \frac{2N}{p(1-p)} = 0, \quad m(0) = m(1) = 0,$$
so $u(p) = \dfrac{1 - e^{-\alpha p}}{1 - e^{-\alpha}}$ (Kimura). Let $\mathrm{Ei}(x) = -\int_{-x}^{\infty} \frac{e^{-t}}{t}\,dt$ be the exponential integral and $\gamma$ the Euler–Mascheroni constant.

**Theorem.** For $\alpha \ne 0$,
$$m(p) = 2N\big(\omega(\alpha, p) + \omega(-\alpha, 1-p)\big),$$
$$\alpha\,\omega(\alpha, p) = u(p)\big(\ln|\alpha| + \gamma - e^{-\alpha}\mathrm{Ei}(\alpha)\big) - \big(\ln|\alpha p| + \gamma - e^{-\alpha p}\mathrm{Ei}(\alpha p)\big),$$
equivalently
$$\alpha\,\omega(\alpha, p) = \left[\frac{1 - e^{-\alpha p}}{1 - e^{-\alpha x}}\; e^{-\alpha x}\int_0^{\alpha x} \ln|z|\,e^{z}\,dz\right]_{x=p}^{x=1}.$$
Analogous closed forms in terms of $\mathrm{Ei}$ hold for the conditional mean times to fixation and to loss, obtained from $M_1'' + \alpha M_1' + \frac{2N}{p(1-p)}u = 0$ and $M_0'' + \alpha M_0' + \frac{2N}{p(1-p)}(1-u) = 0$ with $M_1 = u\,m_1$, $M_0 = (1-u)\,m_0$, and truncating the exponential-integral series gives polynomial-logarithmic approximations $m_{(k)}$ that satisfy the boundary conditions.

## Expansion

The equations come from first-step analysis: $m(p) = 1 + \mathbb{E}\,m(p + \Delta p)$, expanded to second order with $\mathbb{E}\Delta p \approx s\,p(1-p)$ and $\mathrm{Var}\,\Delta p \approx p(1-p)/N$, and then rescaled. With integrating factor $e^{\alpha p}$ the ODE for $m$ reduces to integrals of $e^{\alpha x}/(x(1-x))$; partial fractions split $\frac{1}{x(1-x)} = \frac1x + \frac1{1-x}$, and each piece integrates to an exponential integral, which produces the symmetric form $\omega(\alpha, p) + \omega(-\alpha, 1-p)$. As $\alpha \to 0$ the formula recovers the neutral result $m(p) = -2N\big(p\ln p + (1-p)\ln(1-p)\big)$.

## Sources

- V. Runge, A. Liehrmann and P. Spinga, "Exponential Integral Solutions for Fixation Time in Wright-Fisher Model With Selection", arXiv:2205.06480 (2022), Propositions 1 and 2 (Section 2), Theorems 1 and 2 (Section 3), Theorem 3 (Section 4), <https://doi.org/10.48550/arXiv.2205.06480>.
