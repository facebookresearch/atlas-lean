# Logarithmic front corrections for Fisher–KPP in a shifting environment

**Model.** A population of density $n(t,x)$ on $\mathbb{R}$ grows in a habitat whose quality moves to the right with a climate shift $s(t) = \mathfrak{s}t - \eta\ln(1+t)$, $\mathfrak{s} \ge 0$, $\eta \in \mathbb{R}$:

$$ n_t - n_{xx} = n\big(\mathbf{g}(x - s(t)) - n\big), \qquad t > 0,\ x \in \mathbb{R}, $$

with $n_0 \in L^\infty(\mathbb{R};[0,1])$, $\liminf_{x\to-\infty} n_0 > 0$ and $n_0 = 0$ on $[x_0,\infty)$ for some $x_0 > 0$. The growth profile satisfies (G1) $\mathbf{g} \in L^\infty$ is increasing with $\mathbf{g}(-\infty) = 1-a$, $\mathbf{g}(+\infty) = 1$ for some $a \in (0,1)$ (better habitat ahead of the interface), and (G2) $|\mathbf{g}(y) - (1-a)| \in L^1((-\infty,0))$ and $y|1 - \mathbf{g}(y)| \in L^1((0,\infty))$. For $\nu \in \{1-a, 1\}$ let $\Phi_\nu$ be the travelling wave $\Phi_\nu'' + c_\star\Phi_\nu' + \Phi_\nu(\nu - \Phi_\nu) = 0$, $\Phi_\nu(-\infty) = \nu$, $\Phi_\nu(+\infty) = 0$, and set $\mathfrak{s}_c = 2(\sqrt a + \sqrt{1-a})$.

**Theorem.** In each case below there is a bounded $\Lambda : \mathbb{R}^+ \to \mathbb{R}$ such that $n(t,x) - \Phi_\nu\big(x - c_\star t + \ell(t) + \Lambda(t)\big) \to 0$ as $t \to \infty$, uniformly in $x \in \mathbb{R}$ (in cases 1 and 2, uniformly on $x \ge s(t) + \gamma\ln t$ for every $\gamma > 0$):
1. **Slow shift, $\mathfrak{s} < 2$** (here it suffices that $\inf\mathbf{g} > 0$, $\sup_{x\ge x_0}\mathbf{g} \le 1$ and $1 - \inf_{x'\ge x}\mathbf{g}(x') \in L^1((x_0,\infty))$): $\nu = 1$, $c_\star = 2$, $\ell(t) = \tfrac32\ln t$, the classical Bramson correction.
2. **$\mathfrak{s} = 2$, $\eta > 3/2$**: again $\nu = 1$, $c_\star = 2$, $\ell(t) = \tfrac32\ln t$; the level sets satisfy $\xi_\kappa(t) = 2t - \tfrac32\ln(1+t) + O(1)$ and lie $(\eta - \tfrac32)\ln t + O(1)$ ahead of $s(t)$.
3. **Nonlocal pulling, $2 < \mathfrak{s} < \mathfrak{s}_c$ (any $\eta$) or $\mathfrak{s} = 2$, $\eta < 3/2$**: $\nu = 1 - a$, $\lambda_\star = \mathfrak{s}/2 - \sqrt a$, $c_\star = \lambda_\star + (1-a)/\lambda_\star$, and $\ell(t) = \lambda_\star^{-1}\big(\tfrac32 - \eta\sqrt a\big)\ln t$. The front lags behind the shift (by order $(\mathfrak{s} - c_\star)t$, respectively $\ln t$) yet moves faster than $2\sqrt{1-a}$: it is pulled by the favourable habitat ahead.
4. **Critical pulling, $\mathfrak{s} = \mathfrak{s}_c$**: $\nu = 1-a$, $\lambda_\star = \sqrt{1-a}$, $c_\star = 2\sqrt{1-a}$ and

$$ \ell(t) = \begin{cases} \tfrac{3}{2\lambda_\star}\ln t, & \eta < -\tfrac{1}{2\sqrt a},\\ \tfrac{3}{2\lambda_\star}\ln t - \tfrac{1}{\lambda_\star}\ln\ln t, & \eta = -\tfrac{1}{2\sqrt a},\\ \tfrac{5/2 - \eta\sqrt a}{2\lambda_\star}\ln t, & \eta > -\tfrac{1}{2\sqrt a}. \end{cases} $$

5. **Fast shift, $\mathfrak{s} > \mathfrak{s}_c$**: $\nu = 1-a$, $c_\star = 2\sqrt{1-a}$, $\ell(t) = \tfrac{3}{2\sqrt{1-a}}\ln t$, the Bramson correction of the poor habitat.

The environmental displacement $\eta\ln t$ changes the front position only in the pulled regimes, where it modifies the Bramson coefficient, and at one critical parameter value it produces an extra $\ln\ln t$ term.

## Depends on

- [A strictly decreasing front exists at the minimal speed](../fisher-kpp-travelling-waves/exists-is-front-two-mul-sqrt.md)

## Expansion

Ahead of the interface, the linearized equation in the frame $x - s(t)$ is a heat equation with a localized potential $1 - \mathbf{g}$. Its spatial corrector, the positive solution $\mathfrak{m}$ of $\mathfrak{m}'' = (1 - \mathbf{g})\mathfrak{m}$ with $\mathfrak{m}'(+\infty) = 1$, plays the role that $x$ plays in the Dirichlet half-line problem behind Bramson's $\tfrac32\ln t$. Sharp Gaussian barriers built from such correctors (for Schrödinger operators), matched to the travelling wave behind the front, give sub- and supersolutions whose positions agree up to $O(1)$. In the pulled regimes the front decays at the rate $\lambda_\star$ set by the favourable region, and the $\eta\ln t$ lag of the environment changes the heat-kernel mass that reaches the front, which produces the coefficients above.

## Sources

- Émeric Bouin, King-Yeung Lam and Chang-Hong Wu, "Logarithmic corrections and interacting fronts in shifting environments and competition systems", arXiv:2610.26702 (2026), Section 1, Theorems 1.1, 1.2, 1.4, 1.5 and 1.6; Section 2 (correctors), <https://doi.org/10.48550/arXiv.2610.26702>.
