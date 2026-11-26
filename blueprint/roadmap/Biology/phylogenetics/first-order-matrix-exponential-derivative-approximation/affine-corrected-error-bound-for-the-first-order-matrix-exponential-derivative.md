# Affine-corrected error bound for the first-order matrix exponential derivative

For $Q, J \in M(d)$, the directional derivative of the matrix exponential satisfies

$$\nabla_J e^{tQ} := \lim_{\epsilon\to 0}\frac{e^{t(Q+\epsilon J)} - e^{tQ}}{\epsilon} = e^{tQ}\int_0^t e^{-sQ} J e^{sQ}\,ds = e^{tQ}\sum_{n=0}^{\infty}\frac{t^{n+1}}{(n+1)!}\sum_{l=0}^{n}(-1)^l\binom{n}{l} Q^l J Q^{n-l},$$

and keeping only $n = 0$ gives the first-order approximation $\tilde\nabla_J e^{tQ} = t\,e^{tQ} J$, exact when $J$ and $Q$ commute. Its error $E(t) = \nabla_J e^{tQ} - t e^{tQ}J$ solves $\dot E = QE + Je^{tQ} - e^{tQ}J$, $E(0) = 0$, so

$$E(t) = e^{tQ}\int_0^t \left(e^{-sQ}Je^{sQ} - J\right)ds .$$

**Theorem.** Suppose $Q^+ \in M(d)$ satisfies $Q^+QQ^+ = Q^+$, $QQ^+ = Q^+Q$, $e^{\tau Q}(I - Q^+Q) = I - Q^+Q$ and $(I - QQ^+)e^{\tau Q} = I - QQ^+$ for all real $\tau$, and that $\|Qe^{\tau Q}\| \le C_0 e^{-\kappa\tau}$ for all $\tau \ge 0$ in some matrix norm, with constants $C_0, \kappa > 0$. Then for all $t \ge 0$,

$$\left\| Q^+J(I - QQ^+) - (I - Q^+Q)JQ^+ + t(I - Q^+Q)JQQ^+ + \nabla_J e^{tQ} - t e^{tQ}J \right\| \le C(1+t)e^{-\kappa t},$$

with $C = C_0\left(\|(I-Q^+Q)J(Q^+)^2\| + \|(Q^+)^2J(I-QQ^+)\| + \|Q^+J\|\right) + C_0^2\|Q^+JQ^+\|$.

The hypotheses hold, for instance, for a symmetric $Q$ with nonpositive eigenvalues and $Q^+$ its Moore–Penrose inverse, and for diagonalizable $Q$ with spectrum in the open left half-plane or at the origin. For symmetric nonpositive $Q$ with $\lambda_d(Q) = 0$ and nonzero eigenvalues of modulus between $\mu_1 d$ and $\mu_2 d$, the operator-norm error of the corrected approximation obeys

$$\left\| t(I - Q^+Q)JQQ^+ + \nabla_J e^{tQ} - t e^{tQ}J \right\|_{op} \le \left(\frac{\mu_2}{\mu_1^2}\left[\frac{2}{d} + \mu_1 + \mu_2\right]\,(1+t)e^{-t\mu_1 d} + \frac{2}{\mu_1 d}\right)\|J\|_{op}.$$

## Expansion

Differentiating $e^{t(Q+\epsilon J)}$ in $\epsilon$ gives the linear inhomogeneous ODE $\dot Y = QY + Je^{tQ}$, whose variation-of-constants solution is the integral formula; expanding both exponentials and integrating term by term produces the series. Splitting the integrand with the projections $Q^+Q$ and $I - Q^+Q$ separates a part on which $Qe^{\tau Q}$ decays exponentially from the kernel part, where $e^{\tau Q}$ acts as the identity and contributes the terms that are constant or linear in $t$. The dimensional bound comes from bounding $\|Q^+\|_{op} \le 1/(\mu_1 d)$ and $|\lambda_1(Q)| \le \mu_2 d$.

## Sources

- G. Didier, N. E. Glatt-Holtz, A. J. Holbrook, A. F. Magee and M. A. Suchard, "On the surprising effectiveness of a simple matrix exponential derivative approximation, with application to global SARS-CoV-2", *Proceedings of the National Academy of Sciences* 121 (2024), e2318989121, Eqs. (2)–(4) and (12)–(19), Theorem 1 with Remark 1, and Theorem 2, Eq. (39). <https://doi.org/10.1073/pnas.2318989121> (PMC10801879)
