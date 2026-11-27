# Critical lockdown intensity for stopping an epidemic at herd immunity

**Setting.** As in [Optimal onset of a fixed-duration lockdown in the SIR model](optimal-onset-of-a-fixed-duration-lockdown-in-the-sir-model.md): controlled SIR dynamics $\dot S = -u \beta S I$, $\dot I = u\beta S I - \gamma I$ with $\mathcal{R}_0 = \beta/\gamma > 1$, herd immunity threshold $S_{\mathrm{herd}} = 1/\mathcal{R}_0$, lockdown intensity bound $\alpha \in [0,1)$, maximal duration $D$, and optimal final susceptible fraction $S^*_\infty(\alpha, D)$ over all onsets and admissible inputs.

**Theorem.** For $S_0 \in (S_{\mathrm{herd}}, 1)$ and $I_0 > 0$ define

$$\bar\alpha = \frac{S_{\mathrm{herd}}}{S_0 + I_0 - S_{\mathrm{herd}}\big(\ln S_0 - \ln S_{\mathrm{herd}}\big)} .$$

Then $\bar\alpha \in (0, 1)$ and

1. if $\alpha \in [0, \bar\alpha]$, then $\lim_{D \to \infty} S^*_\infty(\alpha, D) = S_{\mathrm{herd}}$: a sufficiently long and intense lockdown stops the epidemic arbitrarily close to herd immunity;
2. if $\alpha \in (\bar\alpha, 1)$, then $\lim_{D \to \infty} S^*_\infty(\alpha, D) = S_\infty(\alpha \mathbf{1}) < S_{\mathrm{herd}}$, the final susceptible fraction of the epidemic run permanently at reduced contact rate $\alpha\beta$: the overshoot below herd immunity cannot be removed by lengthening the lockdown.

## Depends on

- [Optimal onset of a fixed-duration lockdown in the SIR model](optimal-onset-of-a-fixed-duration-lockdown-in-the-sir-model.md)
- [Limits and final size of the SIR epidemic](../../global-behaviour-of-the-sir-model/tendsto-final-size.md)

## Expansion

Positivity of $\bar\alpha$ uses $S_0 > S_{\mathrm{herd}}$, and $\bar\alpha < (S_0/S_{\mathrm{herd}} - 1)^{-1}\ln(S_0/S_{\mathrm{herd}}) < 1$ since $\ln x < x - 1$ for $x > 1$. The proof rests on an earlier result for lockdowns starting at time $0$ (Bliman, Duprez, Privat and Vauchelet, 2020, Theorem 1): for $\alpha \le \bar\alpha$ and every $\varepsilon > 0$ some duration $D$ and some $u \in \mathcal{U}_{\alpha, 0, D}$ give $S_\infty(u) \in [S_{\mathrm{herd}} - \varepsilon, S_{\mathrm{herd}}]$, while for $\alpha > \bar\alpha$ every such input gives $S_\infty(u) \le S_\infty(\alpha\mathbf{1})$. The constant $\bar\alpha$ comes from the conserved quantity $S + I - S_{\mathrm{herd}} \ln S$ of the uncontrolled flow. Combined with monotonicity of the optimal value in $D$ and $S^*_\infty \le S_{\mathrm{herd}}$, this gives both limits.

## Sources

- P.-A. Bliman and M. Duprez, "How best can finite-time social distancing reduce epidemic final size?", Journal of Theoretical Biology 511 (2021), 110557, Theorem 3 and Eq. (7), <https://doi.org/10.1016/j.jtbi.2020.110557> (PMCID: PMC7833531).
