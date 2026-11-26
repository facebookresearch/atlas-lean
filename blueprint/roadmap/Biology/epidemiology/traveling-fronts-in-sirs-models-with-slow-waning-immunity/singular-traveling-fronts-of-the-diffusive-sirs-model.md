# Singular traveling fronts of the diffusive SIRS model

**Model.** With total population normalized to $1$, diffusion of infected individuals only, and time and space rescaled by the recovery rate and diffusivity,
$$S_t = -\mathcal R_0SI + \delta R, \qquad I_t = \mathcal R_0SI - I + I_{xx}, \qquad R_t = I - \delta R,$$
where $\mathcal R_0 > 1$ and $0 < \delta \ll 1$ is the ratio of the immunity-loss rate to the recovery rate. The homogeneous equilibria are the disease-free state $(1,0,0)$ and the endemic state $\big(\tfrac1{\mathcal R_0}, \tfrac{\delta}{1+\delta}\tfrac{\mathcal R_0 - 1}{\mathcal R_0}, \tfrac{1}{1+\delta}\tfrac{\mathcal R_0-1}{\mathcal R_0}\big)$.

**Traveling-wave reduction.** With $\xi = -(x - ct)$, $J = dI/d\hat\xi$ and the conserved quantity $c(S + I + R) + J = c$, fronts solve the singularly perturbed system in non-standard form
$$\frac{dS}{d\xi} = \frac1c\Big[\delta(1 - S - I) - \mathcal R_0SI - \frac\delta cJ\Big], \qquad \frac{dI}{d\xi} = -J, \qquad \frac{dJ}{d\xi} = cJ + \mathcal R_0SI - I.$$
For $\delta = 0$ (layer problem) the critical manifold is $\mathcal C_0 = \{I = J = 0\}$, and $\Gamma(S,I,J) = -\frac{c}{\mathcal R_0}\log S + c(S + I) + J$ is a constant of motion; on $\mathcal C_0$ the slow flow in $\zeta = \delta\xi$ is $dS/d\zeta = (1 - S)/c$.

**Results.**

1. *Linearization.* At the disease-free state one eigenvalue is real, negative and $O(\delta)$, the other two have positive $O(1)$ real part and are real iff $c^2 \ge 4(\mathcal R_0 - 1)$; this defines $c_{\mathrm{crit}} = 2\sqrt{\mathcal R_0 - 1}$. At the endemic state, for small $\delta$, there is one real positive $O(1)$ eigenvalue and a complex pair with negative $O(\delta)$ real part.
2. *Fast excursions.* There is a unique $L \in (0, 1/\mathcal R_0)$ such that layer orbits starting near $(S, 0, 0)$ with $S \in (1/\mathcal R_0, 1]$ return to $\mathcal C_0$ at a point with $S \in [L, 1/\mathcal R_0)$, determined by the second root of $-\frac1{\mathcal R_0}\log x + x = -\frac1{\mathcal R_0}\log S_1 + S_1$.
3. *Singular front.* In the limit $\delta \to 0$ there is at least one speed $c \ge c_{\mathrm{crit}}$ with a singular front orbit joining the endemic state (behind) to the disease-free state (ahead), formed by concatenating fast outbreak excursions along level sets of $\Gamma$, slow drifts along the attracting and repelling branches of $\mathcal C_0$ governed by an entry-exit relation, and a final local spiral into the endemic state.
4. *Entry-exit threshold.* For $c > c_{\mathrm{crit}}$ there is a unique $S^*_\infty \in (1/\mathcal R_0, 1)$ such that the sign condition used in the entry-exit computation of the slow passage holds exactly for entry values $S_\infty < S^*_\infty$, and not on the whole interval $(1/\mathcal R_0, 1)$.

## Depends on

- [No Fisher-KPP traveling front with $c^2 < 4rD$](../../pattern-formation/fisher-kpp-travelling-waves/not-is-front-of-sq-lt.md)

## Expansion

Ahead of the front the linearization at the disease-free state is that of a Fisher-KPP equation with growth rate $\mathcal R_0 - 1$, so speeds below $2\sqrt{\mathcal R_0 - 1}$ give oscillating, sign-changing infected profiles; numerically the front selects $c_{\mathrm{crit}}$. Behind the leading edge the dynamics alternate between fast epidemic waves, which follow the planar SIR constant of motion and leave susceptibles at $S_\infty < 1/\mathcal R_0$, and long slow phases in which waning immunity rebuilds susceptibles until the entry-exit (delayed loss of stability) relation triggers the next outbreak. The number of such loops before the orbit settles near the endemic state is controlled by the entry-exit mechanism, which produces the oscillatory wake behind the front.

## Sources

- R. Della Marca, G. Grifo, A. Iuorio and M. Sensi, "Traveling fronts in a spatial epidemic model with slow loss of immunity", arXiv preprint (2026), Section 3, Lemmas 3.1 and 3.3 and Propositions 3.5, 3.6 and 3.9. <https://doi.org/10.48550/arXiv.2608.04594>