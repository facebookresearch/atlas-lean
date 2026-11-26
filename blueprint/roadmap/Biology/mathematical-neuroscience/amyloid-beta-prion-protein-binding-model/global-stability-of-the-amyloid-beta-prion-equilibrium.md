# Global stability of the amyloid-beta-prion equilibrium

**Model.** Soluble $A\beta$ oligomers $u$, cellular prion protein $PrP^C$ $p$, the $A\beta$-$PrP^C$ complex $b$ and insoluble plaques $A$ satisfy

$$\dot A = \alpha u^n - \mu A, \qquad \dot u = \lambda_u - \gamma_u u - \tau up + \sigma b - \alpha n u^n - \rho uA,$$

$$\dot p = \lambda_p - \gamma_p p - \tau up + \sigma b, \qquad \dot b = \tau up - (\sigma + \delta)b,$$

with production rates $\lambda_u,\lambda_p$, degradation rates $\gamma_u,\gamma_p,\delta$, binding/unbinding rates $\tau,\sigma$, plaque formation from $n$ oligomers at rate $\alpha$, plaque-driven oligomer loss $\rho$ and plaque clearance $\mu$. All parameters are positive and states lie in $\mathbb{R}^4_+$.

**Theorem.** The unique positive equilibrium $\tilde E = (\tilde A,\tilde u,\tilde p,\tilde b)$ is globally asymptotically stable on the positively invariant region, for all parameter values.

**Early-stage system.** With plaque formation negligible ($\alpha = 0$), $A(t) = A_0e^{-\mu t} \to 0$, and the limiting system

$$\dot u = \lambda_u - \gamma_u u - \tau up + \sigma b, \qquad \dot p = \lambda_p - \gamma_p p - \tau up + \sigma b, \qquad \dot b = \tau up - (\sigma + \delta)b$$

leaves $\Gamma = \{u + p + 2b \le \lambda/\tilde m\}$ invariant, $\lambda = \lambda_u + \lambda_p$, $\tilde m = \min\{\gamma_u,\gamma_p,\delta\}$, keeps positive data positive, and has a unique positive steady state $E^* = (u^*,p^*,b^*)$ that is globally asymptotically stable.

## Expansion

At equilibrium the complex is $b = \tau up/(\sigma+\delta)$, so the net binding flux is $\tau up\,\delta/(\sigma+\delta)$, and $u$, $p$ each solve a monotone scalar balance, giving uniqueness. The earlier literature had local stability only. The source upgrades this to global stability on the bounded invariant set, where the unique equilibrium attracts every trajectory; for the non-autonomous early-stage model, asymptotically autonomous systems theory transfers the conclusion from the limiting system. Biologically, $A\beta$-$PrP^C$ binding settles to a fixed set point rather than oscillating, whatever the rates.

## Sources

- R. Lang, H. Zhou, "Global stability analysis of a mathematical model from Alzheimer's disease" (2026), systems (1.2) and (upb), Theorem 1.1, Proposition 2.1, Theorems 2.2-2.3, <https://doi.org/10.48550/arXiv.2606.29191>.
