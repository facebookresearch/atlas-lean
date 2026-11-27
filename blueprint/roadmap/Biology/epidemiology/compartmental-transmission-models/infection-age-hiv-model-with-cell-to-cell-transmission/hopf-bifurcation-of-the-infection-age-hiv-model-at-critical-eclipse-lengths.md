# Hopf bifurcation of the infection-age HIV model at critical eclipse lengths

For the infection-age HIV model with logistic T-cell proliferation, virus-to-cell rate $\beta_1$, cell-to-cell rate $\beta_2$ and an eclipse period $\tau$ before infected cells become infectious, linearization at the positive equilibrium (after rescaling time and age by $\tau$) leads to the characteristic equation

$$ g(\zeta) = \zeta^3 + p_2\zeta^2 + p_1\zeta + p_0 + (q_2\zeta^2 + q_1\zeta + q_0)\, e^{-\tau\zeta} = 0 , $$

with explicit coefficients depending on $\Lambda, \mu, r, K, \beta_1, \beta_2, \sigma, N, c$; in particular $q_2 = -c\sigma\beta_2/(N\beta_1 + c\beta_2) < 0$ and $q_1 < 0$, so the delayed terms are driven entirely by cell-to-cell transmission. A purely imaginary root $\zeta = i\omega$ requires $\theta = \omega^2$ to solve

$$ \theta^3 + C_2\theta^2 + C_1\theta + C_0 = 0, \qquad C_2 = p_2^2 - q_2^2 - 2p_1, \quad C_1 = p_1^2 - q_1^2 - 2p_2p_0 + 2q_2q_0, \quad C_0 = p_0^2 - q_0^2 . $$

**Theorem.** Assume the step-infectivity normalization and that $Q > 0$ (positive equilibrium), the cubic discriminant vanishes with $q > 0$ (so the cubic has a single positive double root $\theta_0$), and $C_2 > 0$, $C_1 > 0$. Let $\omega_0 = \sqrt{\theta_0}$. Then there is an increasing sequence of critical eclipse lengths $\tau_k$, $k = 1, 2, \dots$, given by an explicit arccos formula in $\omega_0$ and the coefficients, at which $\pm i\omega_0$ are simple roots of $g$ with transversality

$$ \frac{d\,\mathrm{Re}\,\zeta}{d\tau}\Big|_{\tau = \tau_k} > 0 , $$

and the model undergoes a Hopf bifurcation at the positive equilibrium: a nontrivial periodic solution bifurcates from it at $\tau = \tau_k$.

## Depends on

- [Infection-age HIV model with virus-to-cell and cell-to-cell transmission](infection-age-hiv-model-with-virus-to-cell-and-cell-to-cell-transmission.md)

## Expansion

Separating real and imaginary parts of $g(i\omega) = 0$ and adding squares eliminates $\tau$ and gives the sextic in $\omega$, i.e. the cubic in $\theta$. Since $C_0 = (p_0+q_0)(p_0-q_0) > 0$ when $Q > 0$, the product of the cubic roots is negative. Simplicity of $i\omega_0$ follows because $g'(i\omega_0) = 0$ would force $q_1 = 0$, contradicting $q_1 < 0$. The sign of the crossing speed equals the sign of $3\omega_0^4 + 2C_2\omega_0^2 + C_1$, positive under the hypotheses. The Hopf theorem for non-densely defined Cauchy problems (integrated semigroup theory) then yields the periodic orbits.

## Sources

- Xiangming Zhang, Zhihua Liu, "Bifurcation Analysis of an Age Structured HIV Infection Model with Both Virus-to-Cell and Cell-to-Cell Transmissions", International Journal of Bifurcation and Chaos 28 (2018), 1850109, <https://doi.org/10.1142/s0218127418501092>. Published version of arXiv:1711.02739, cited next; locators there refer to the arXiv version.
- X. Zhang, Z. Liu, "Bifurcation analysis of an age structured HIV infection model with both virus-to-cell and cell-to-cell transmissions", arXiv:1711.02739 (2017), Section 2.3 (characteristic equation) and Section 3, Assumption 3.1, Lemmas 3.1–3.2 and Theorem 3.1. <https://doi.org/10.48550/arXiv.1711.02739>
