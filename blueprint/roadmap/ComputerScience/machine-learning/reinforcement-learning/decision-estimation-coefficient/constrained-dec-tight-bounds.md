# Constrained DEC gives tight expected-regret bounds with improper reference models

Define the **constrained DEC**

$$
\mathrm{dec}^{c}_{\varepsilon}(\mathcal{M}, \bar M) = \inf_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}} \Big\{ \mathbb{E}_{\pi \sim p}\big[f^M(\pi_M) - f^M(\pi)\big] \;:\; \mathbb{E}_{\pi \sim p} D_H^2\big(M(\pi), \bar M(\pi)\big) \le \varepsilon^2 \Big\},
$$

and $\mathrm{dec}^c_\varepsilon(\mathcal{M}) = \sup_{\bar M} \mathrm{dec}^c_\varepsilon(\mathcal{M} \cup \{\bar M\}, \bar M)$ over arbitrary (possibly improper) reference models $\bar M$. Then every algorithm has expected regret $\Omega\big(T\cdot\mathrm{dec}^c_{\varepsilon_T}(\mathcal{M})\big)$ with $\varepsilon_T \asymp 1/\sqrt{T}$, without localization and with no restriction on the algorithm, and there is an algorithm with regret $O\big(T\cdot\mathrm{dec}^c_{\bar\varepsilon_T}(\mathcal{M})\big)$ with $\bar\varepsilon_T \asymp \sqrt{\log|\mathcal{M}|/T}$ up to logarithmic factors, in both the regret and the PAC frameworks. Improper reference models are necessary: restricting to $\bar M \in \mathcal{M}$ can make the lower bound vacuous.

## Proof sketch

The lower bound is a two-point argument with the reference model as the null: if the algorithm's decision distribution under $\bar M$ gathers less than $\varepsilon_T^2$ Hellinger information against each alternative per round, the alternative cannot be detected in $T$ rounds, and the constrained DEC guarantees an alternative with large regret. The upper bound runs a constrained version of E2D that keeps a confidence set of models consistent with the data in Hellinger distance and plays the constrained minimax distribution against the oracle's estimate.

## Depends on

- [Decision making with structured observations](decision-making-structured-observations.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [The localized DEC lower bounds the regret of every algorithm](dec-regret-lower-bound.md)
- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](e2d-regret-upper-bound.md)

## Sources

- D. J. Foster, N. Golowich, Y. Han, "Tight Guarantees for Interactive Decision Making with the Decision-Estimation Coefficient", COLT (2023), arXiv:2301.08215.
