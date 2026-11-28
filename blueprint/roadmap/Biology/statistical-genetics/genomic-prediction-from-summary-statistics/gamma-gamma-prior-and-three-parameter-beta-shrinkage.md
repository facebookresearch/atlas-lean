# Gamma–gamma local shrinkage prior and the three-parameter beta law of the shrinkage factor (PRS-CS)

Consider standardized phenotypes $y = Z\beta + \varepsilon$, $\varepsilon \sim N(0, \sigma^2 I_N)$, with $N$ individuals and $M$ standardized markers, and the global–local scale-mixture prior

$$\beta_j \mid \sigma^2, \phi, \psi_j \sim N\!\Big(0, \frac{\sigma^2}{N}\phi\psi_j\Big), \qquad \psi_j \mid \delta_j \sim \mathrm{Gamma}(a, \text{rate } \delta_j), \qquad \delta_j \sim \mathrm{Gamma}(b, \text{rate } 1),$$

with $a, b, \phi > 0$, independently over $j$. Let $\hat\beta = Z^\top y / N$ be the marginal least-squares estimates and $D = Z^\top Z / N$ the LD matrix.

**Posterior mean.** Given $(\sigma^2, \phi, \psi)$, $E[\beta \mid \hat\beta] = (D + T^{-1})^{-1}\hat\beta$ with $T = \operatorname{diag}(\phi\psi_1, \dots, \phi\psi_M)$. If $D = I$ (unlinked markers), $E[\beta_j \mid \hat\beta_j] = (1 - \tau_j)\hat\beta_j$ with shrinkage factor $\tau_j = 1/(1 + \phi\psi_j) \in (0,1)$.

**Proposition (TPB representation).** Marginally over $\delta_j$, the shrinkage factor $\tau_j$ has the three-parameter beta density

$$f(x; a, b, \phi) = \frac{\Gamma(a+b)}{\Gamma(a)\Gamma(b)}\,\phi^{b}\,x^{b-1}(1-x)^{a-1}\{1 + (\phi - 1)x\}^{-(a+b)}, \qquad 0 < x < 1.$$

For $\phi = 1$ this is $\mathrm{Beta}(b, a)$. The parameter $a$ governs the mass of $\tau_j$ near $1$ (the spike of the prior on $\beta_j$ at zero), $b$ the mass near $0$ (the tails), and decreasing $\phi$ moves mass toward $\tau_j = 1$ (stronger shrinkage). The choice $a = b = 1/2$ is the horseshoe prior; PRS-CS uses the Strawderman–Berger choice $a = 1$, $b = 1/2$.

## Expansion

Integrating $\delta_j$ out of the gamma–gamma hierarchy gives the beta-prime law $p(\psi) = \psi^{a-1}(1+\psi)^{-(a+b)}/B(a,b)$. With $\psi = (1-x)/(\phi x)$ one has $|d\psi/dx| = 1/(\phi x^2)$ and $1 + \psi = \{1 + (\phi - 1)x\}/(\phi x)$; substituting, the powers of $\phi$ collect to $\phi^{b}$ and the powers of $x$ to $x^{b-1}$, which is the displayed density. The posterior mean formula follows from conjugate Gaussian algebra with $Z^\top Z = ND$ and $Z^\top y = N\hat\beta$; for $D = I$ it reads $\hat\beta_j/(1 + \phi^{-1}\psi_j^{-1})$. The rate parameterization of the gamma hierarchy is the one under which this change of variables holds.

## Sources

- T. Ge, C.-Y. Chen, Y. Ni, Y.-C. A. Feng and J. W. Smoller, "Polygenic prediction via Bayesian regression and continuous shrinkage priors", Nature Communications 10 (2019), 1776, Methods "PRS-CS and PRS-CS-auto", Equations 5–11, <https://doi.org/10.1038/s41467-019-09718-5> (PMC6467998).
- A. Armagan, D. B. Dunson and M. Clyde, "Generalized beta mixtures of Gaussians", Advances in Neural Information Processing Systems 24 (2011) (three-parameter beta family).
