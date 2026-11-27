# Lyapunov limit of the non-equilibrium potential under power-like kinetics

**Setting.** Let $\{\mathcal S, \mathcal C, \mathcal R\}$ be a reaction network with rate constants $\{\kappa_k\}$ whose deterministic mass-action model is complex balanced with equilibrium $c \in \mathbb R^m_{>0}$. Assume each association function $\theta_i : \mathbb Z \to \mathbb R_{\ge 0}$ satisfies $\theta_i(x) = 0$ for $x \le 0$ and behaves like a power at infinity:

$$\lim_{x\to\infty}\frac{\theta_i(x)}{x^{d_i}} = A_i, \qquad d, A \in \mathbb R^m_{>0}.$$

For a scaling parameter $V > 0$, set $\kappa_k^V = \kappa_k / V^{d\cdot y_k - 1}$ and use the intensities $\lambda_k^V(x) = \kappa_k^V\prod_i\theta_i(x_i)\cdots\theta_i(x_i - y_{ki} + 1)$. The stochastic model then has stationary measure $\pi^V_*(x) = \prod_i (V^{d_i}c_i)^{x_i}/(\theta_i(1)\cdots\theta_i(x_i))$, summable since $\theta_i \to \infty$. Let $\tilde\pi^V(\tilde x) = \pi^V(V\tilde x)$, $\tilde x \in V^{-1}\mathbb Z^m_{\ge 0}$, be the normalized stationary distribution of the scaled process $V^{-1}X^V$. The non-equilibrium potential is $-\ln\tilde\pi^V$.

**Lemma.** The ODE

$$\dot x = \sum_k \kappa_k\,(Ax^d)^{y_k}\,(y_k' - y_k), \qquad (Ax^d)_i = A_ix_i^{d_i},$$

is complex balanced with equilibrium $\tilde c_i = (c_i/A_i)^{1/d_i}$.

**Theorem.** For every sequence $\tilde x^V \in V^{-1}\mathbb Z^m_{\ge 0}$ with $\tilde x^V \to \tilde x$, $\tilde x$ having positive coordinates,

$$\lim_{V\to\infty}\Big[-\frac1V\ln\tilde\pi^V(\tilde x^V)\Big] = \mathcal V(\tilde x) = \sum_{i=1}^m \tilde x_i\big(d_i\ln\tilde x_i - \ln c_i - d_i + \ln A_i\big) + \sum_{i=1}^m d_i\Big(\frac{c_i}{A_i}\Big)^{1/d_i},$$

and $\mathcal V$ is a Lyapunov function for the ODE above at $\tilde c$. With $d = A = (1, \dots, 1)$ this is the mass-action result: the scaled potential converges to the classical Lyapunov function $\sum_i x_i(\ln x_i - \ln c_i - 1) + c_i$ of chemical reaction network theory.

## Depends on

- [Product-form stationary measures under non-mass-action kinetics force complex balance](product-form-stationary-measures-under-non-mass-action-kinetics-force-complex-balance.md)
- [Complex-balanced concentrations](../../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

The potential splits over species. For each species, $-\frac1V\ln\big[(V^{d_i}c_i)^{V\tilde x_i}/\prod_{j\le V\tilde x_i}\theta_i(j)\big]$ is evaluated with $\ln\theta_i(j) = d_i\ln j + \ln A_i + o(1)$ and a Stirling-type sum $\sum_{j\le n}\ln j = n\ln n - n + O(\ln n)$. This produces $\tilde x_i(d_i\ln\tilde x_i - \ln c_i - d_i + \ln A_i)$. The normalizing constant contributes the constant term, as a Laplace-type limit of the same expression maximized at $\tilde c_i$. The Lyapunov property is the standard complex-balanced computation applied to the ODE with kinetics $Ax^d$, whose equilibrium $\tilde c$ minimizes $\mathcal V$.

## Sources

- David F. Anderson and Tung D. Nguyen, "Results on stochastic reaction networks with non-mass action kinetics", Mathematical Biosciences and Engineering 16 (2019), 2118–2140, <https://doi.org/10.3934/mbe.2019103>; numbering as in arXiv:1712.01716: Theorems 3.4 and 3.5, Theorem 4.3, Assumption 1, Lemma 4.2, Theorem 4.4.
