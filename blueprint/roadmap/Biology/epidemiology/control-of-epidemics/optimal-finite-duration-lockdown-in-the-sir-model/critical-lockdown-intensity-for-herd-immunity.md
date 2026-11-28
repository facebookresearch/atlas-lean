# Critical lockdown intensity for reaching herd immunity with long interventions

In the controlled SIR model $\dot S = -u \beta S I$, $\dot I = u \beta S I - \gamma I$ with $\mathcal{R}_0 = \beta/\gamma > 1$ and $S_{\mathrm{herd}} = 1/\mathcal{R}_0$, let $S^*_\infty(D)$ be the largest achievable limit of susceptibles (smallest final size) using a social-distancing control $u \in [\alpha, 1]$ on a window of duration $D$ and $u = 1$ elsewhere, with lockdown intensity bound $\alpha \in [0,1)$.

**Theorem.** Let $S_0 \in (S_{\mathrm{herd}}, 1)$ and $I_0 > 0$, and define

$$\bar\alpha = \frac{S_{\mathrm{herd}}}{S_0 + I_0 - S_{\mathrm{herd}}} \bigl(\ln S_0 - \ln S_{\mathrm{herd}}\bigr).$$

Then $\bar\alpha \in (0,1)$ and:

1. if $\alpha \in [0, \bar\alpha]$, then $\lim_{D \to \infty} S^*_\infty(D) = S_{\mathrm{herd}}$: a sufficiently long lockdown stops the epidemic arbitrarily close to the herd-immunity threshold;
2. if $\alpha \in (\bar\alpha, 1)$, then $\lim_{D \to \infty} S^*_\infty(D) = S_\infty(\alpha) < S_{\mathrm{herd}}$, the final susceptible level of the epidemic run permanently at reduced contact rate $\alpha \beta$: too mild a lockdown has an intrinsic limit, however long it lasts.

Note that $\bar\alpha$ is the value of $\alpha$ for which the trajectory with constant $u = \alpha$ ends exactly at $S_{\mathrm{herd}}$, i.e. $\alpha \mathcal{R}_0$ satisfies the classical final-size relation with $S_\infty = S_{\mathrm{herd}}$.

## Proof depends on

- [Optimal timing of a fixed-duration lockdown for the SIR final size](optimal-timing-of-a-fixed-duration-lockdown.md)

## Expansion

Under constant control $u = \alpha$, $\Phi_{\alpha \mathcal{R}_0}(S, I) = S + I - (\alpha\mathcal{R}_0)^{-1}\ln S$ is conserved, so the epidemic with reduced reproduction number $\alpha\mathcal{R}_0$ ends at $S_\infty(\alpha)$ solving $S_\infty - (\alpha \mathcal{R}_0)^{-1} \ln S_\infty = S_0 + I_0 - (\alpha\mathcal{R}_0)^{-1}\ln S_0$. Setting $S_\infty = S_{\mathrm{herd}}$ and solving for $\alpha$ gives $\bar\alpha$. If $\alpha \le \bar\alpha$, a long lockdown can hold the state while $S$ drifts to just above $S_{\mathrm{herd}}$ with $I$ tiny, after which release produces almost no further infections. If $\alpha > \bar\alpha$, even permanent distancing overshoots herd immunity, and the optimal long lockdown approaches that permanent policy.

## Sources

- Pierre-Alexandre Bliman, Michel Duprez, "How Best Can Finite-Time Social Distancing Reduce Epidemic Final Size?", arXiv (2020). Theorem 3. <https://doi.org/10.48550/arXiv.2009.14648> Published version: Journal of Theoretical Biology 511 (2021) 110557, <https://doi.org/10.1016/j.jtbi.2020.110557>.
