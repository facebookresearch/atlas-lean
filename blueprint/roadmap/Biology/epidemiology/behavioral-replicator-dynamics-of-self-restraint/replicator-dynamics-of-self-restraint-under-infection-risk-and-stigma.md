# Replicator dynamics of self-restraint under infection risk and stigma

**Model.** A constant population chooses between going out ($G$) and staying home ($S$); $x(t)$ is the
share going out. Payoffs are

$$\pi_G = u_{\mathrm{out}} - \gamma(x)\, c - (1 + \rho\iota)\,\sigma\, s(x), \qquad \pi_S = u_{\mathrm{home}},$$

with subjective infection probability $\gamma(x) = \eta x$ ($\eta > 0$), infection cost $c > 0$, relative
stigma weight $\sigma > 0$ and stigma cost $s(x) = \zeta_0 - \zeta_1 x$ that falls as more people go out
($\zeta_0 > \zeta_1 > 0$, so $s(1) > 0$). The indicator $\iota \in \{0, 1\}$ marks a non-binding state of
emergency that amplifies stigma by the factor $1 + \rho$, $\rho > 0$. Write
$\Delta = u_{\mathrm{out}} - u_{\mathrm{home}}$ and $\sigma_\iota = (1 + \rho\iota)\sigma$. Shares evolve by the
replicator equation

$$\dot{x} = x(1 - x)(\pi_G - \pi_S) = x(1 - x)\bigl(\Delta - \eta c\, x - \sigma_\iota(\zeta_0 - \zeta_1 x)\bigr).$$

**Proposition (steady states).** The rest points are $0$, $1$ and

$$\hat{x}_\iota = \frac{\Delta - \sigma_\iota \zeta_0}{\eta c - \sigma_\iota \zeta_1},$$

which lies in $(0, 1)$ if and only if $\sigma_\iota \zeta_0 < \Delta < \eta c + \sigma_\iota(\zeta_0 - \zeta_1)$. If
moreover $\eta c > \sigma_\iota \zeta_1$, the interior point is asymptotically stable and $0$, $1$ are
unstable.

**Proposition (effect of a non-binding emergency declaration).** With interior stable points in both
regimes, $\hat{x}_1 < \hat{x}_0$, that is, stigma amplification alone reduces going out, if and only if

$$\Delta < \frac{\zeta_0}{\zeta_1}\, \eta c .$$

**Comparative statics.** The interior share increases with $u_{\mathrm{out}}$ and $\zeta_1$ and decreases
with $u_{\mathrm{home}}$, $\eta$, $c$, $\sigma$, $\zeta_0$ and (under the declaration) $\rho$.

## Expansion

The bracket is affine in $x$, so it has one root; it is decreasing in $x$ exactly when the marginal
infection cost $\eta c$ exceeds the marginal stigma relief $\sigma_\iota \zeta_1$, which makes going out
self-limiting and the interior point an attractor, while the endpoints repel because the bracket is
positive at $0$ and negative at $1$ under the existence conditions. Differentiating $\hat{x}$ in the
stigma weight gives a numerator $\zeta_1 \Delta - \zeta_0 \eta c$, which yields the declaration
criterion: amplifying stigma restrains behavior only when the private gain from going out is small
relative to the infection cost scaled by how strongly stigma depends on others' behavior. Infection
risk here is a perceived, behavior-dependent cost rather than an explicit transmission model.

## Sources

- K. Kurita, S. Managi, "COVID-19 and stigma: evolution of self-restraint behavior", Dynamic Games
  and Applications 12 (2022), Eqs. 1-14, Lemmas 1-2 and Propositions 1-4,
  <https://doi.org/10.1007/s13235-022-00426-2> (PMC8788405).
