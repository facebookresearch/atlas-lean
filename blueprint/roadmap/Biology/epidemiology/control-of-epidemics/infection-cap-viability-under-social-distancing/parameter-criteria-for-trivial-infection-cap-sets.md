# Parameter criteria for trivial admissible and robust invariant sets under an infection cap

For a compartmental epidemic with infection cap $I(t) \le I_{\max}$ on the normalized state space $G_\Pi$ (nonnegative fractions summing to at most 1, with $I \le I_{\max}$), let $\mathcal{A}$ be the admissible set (some admissible intervention keeps the cap forever) and $\mathcal{M}$ the maximal robust positively invariant set (every admissible input or parameter value keeps the cap forever). Always $\mathcal{M} \subseteq \mathcal{A} \subseteq G_\Pi$.

**Proposition (SIR).** For $\dot S = -\beta S I$, $\dot I = \beta S I - \gamma I$ with known $\gamma > 0$ and controllable $\beta(t) \in [\beta_{\min}, \beta_{\max}]$:

- $\mathcal{M} = \mathcal{A} = G_\Pi$ if and only if $\beta_{\max} \le \gamma/(1 - I_{\max})$;
- $\mathcal{M} \subsetneq \mathcal{A} = G_\Pi$ if and only if $\beta_{\max} > \gamma/(1 - I_{\max}) \ge \beta_{\min}$;
- $\mathcal{M} \subsetneq \mathcal{A} \subsetneq G_\Pi$ if and only if $\beta_{\min} > \gamma/(1 - I_{\max})$.

If instead $\gamma(t) \in [\gamma_{\min}, \gamma_{\max}]$ is an uncertain parameter and distancing follows the affine feedback $\hat\beta(I) = \beta_{\max} + (\beta_{\min} - \beta_{\max}) I / I_{\max}$, then $\mathcal{M} = G_\Pi$ if and only if $\beta_{\min} \le \gamma_{\min}/(1 - I_{\max})$.

**Proposition (SEIR).** For $\dot S = -\beta S I$, $\dot E = \beta S I - \eta E$, $\dot I = \eta E - \gamma I$ with known $\eta > 0$ and controllable $\beta(t) \in [\beta_{\min}, \beta_{\max}]$, $\gamma(t) \in [\gamma_{\min}, \gamma_{\max}]$:

- $\mathcal{M} = \mathcal{A} = G_\Pi$ if and only if $\eta (1 - I_{\max}) \le \gamma_{\min} I_{\max}$;
- $\mathcal{M} \subsetneq \mathcal{A} = G_\Pi$ if and only if $\gamma_{\min} I_{\max} < \eta(1 - I_{\max}) \le \gamma_{\max} I_{\max}$;
- $\mathcal{M} \subsetneq \mathcal{A} \subsetneq G_\Pi$ if and only if $\eta(1 - I_{\max}) > \gamma_{\max} I_{\max}$.

With uncertain $\eta \in [\eta_{\min}, \eta_{\max}]$ under the paper's feedback laws for $\beta$ and $\gamma$, $\mathcal{M} = G_\Pi$ if and only if $\eta_{\max}(1 - I_{\max}) \le \gamma_{\max} I_{\max}$.

In words: if even the nominal (or least favorable) dynamics cannot push the infected fraction up at the cap, no intervention is ever needed; if only the strongest intervention can, the cap is attainable from everywhere but not robustly; otherwise some initial states are doomed to breach the cap.

## Proof depends on

- [Barrier of the admissible and robust invariant sets for the SIR infection cap](barrier-of-admissible-and-robust-invariant-sets-for-the-sir-infection-cap.md)

## Expansion

$\mathcal{M} = G_\Pi$ exactly when the vector field points into $G_\Pi$ along its whole boundary for every input. On the faces $S = 0$, $I = 0$ and $S + I = 1$ this holds automatically; on the cap face $I = I_{\max}$ it requires $\max_\beta (\beta S - \gamma) I_{\max} \le 0$ for all $S \in [0, 1 - I_{\max}]$, i.e. $\beta_{\max}(1 - I_{\max}) \le \gamma$. Similarly $\mathcal{A} = G_\Pi$ exactly when some input points inward on the cap face, i.e. $\beta_{\min}(1 - I_{\max}) \le \gamma$. For SEIR the cap face condition involves $\dot I = \eta E - \gamma I$ with $E \le 1 - I_{\max}$, giving the stated inequalities with $\gamma_{\min}$ (robust) and $\gamma_{\max}$ (controlled); the contact rate does not enter because $\dot I$ does not depend on $\beta$ directly.

## Sources

- Willem Esterhuizen, Jean Lévine, Stefan Streif, "Epidemic Management with Admissible and Robust Invariant Sets", arXiv (2021). Proposition 7.1, Proposition 7.2. <https://doi.org/10.48550/arXiv.2109.05754> Published version: PLOS ONE 16 (2021) e0257598, <https://doi.org/10.1371/journal.pone.0257598>.
