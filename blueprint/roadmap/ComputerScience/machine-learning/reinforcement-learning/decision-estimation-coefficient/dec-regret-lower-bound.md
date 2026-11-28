# The constrained DEC lower bounds the regret of every algorithm

For a model class $\mathcal{M}$, a reference model $\bar M$ and a radius $\varepsilon > 0$, the **constrained DEC** is

$$
\mathrm{dec}^{c}_{\varepsilon}(\mathcal{M}, \bar M) = \inf_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}} \Big\{ \mathbb{E}_{\pi \sim p}\big[f^M(\pi_M) - f^M(\pi)\big] \;:\; \mathbb{E}_{\pi \sim p} D_H^2\big(M(\pi), \bar M(\pi)\big) \le \varepsilon^2 \Big\},
$$

where $D_H^2(P, Q) = \int \big(\sqrt{dP/d\nu} - \sqrt{dQ/d\nu}\big)^2\, d\nu = 2\, d_{\mathrm{Hell}}(P, Q)^2$ is the unnormalized squared Hellinger distance, twice the square of the linked Hellinger distance $d_{\mathrm{Hell}}$, as in the offset DEC; the value is $0$ when some $p$ leaves no $M$ satisfying the constraint, and $\mathrm{dec}^c_\varepsilon(\mathcal{M}) = \sup_{\bar M \in \mathrm{co}(\mathcal{M})} \mathrm{dec}^c_\varepsilon(\mathcal{M} \cup \{\bar M\}, \bar M)$. If every model in $\mathcal{M}$ has rewards in $[0,1]$, then for every $T \ge 1$ and every $T$-round algorithm,

$$
\sup_{M \in \mathcal{M}} \mathbb{E}^{M}[\mathrm{Reg}_T] \ge T\Big(\tfrac18\,\mathrm{dec}^c_{\varepsilon}(\mathcal{M}) - 6\varepsilon - \tfrac1T\Big), \qquad \varepsilon = \frac{1}{24\sqrt{T}} .
$$

The bound needs no localization and no restriction on the algorithm. Together with the upper bounds for E2D, it shows that the DEC governs the regret up to the radius of the coefficient and the estimation complexity.

## Proof sketch

Fix $\bar M \in \mathrm{co}(\mathcal{M})$ and run the algorithm under $\bar M$, stopping the averaging of its decision distributions at the first round where its accumulated regret under $\bar M$ reaches a threshold of order $T(R + \varepsilon)$, with $R$ the worst-case average regret. The constrained DEC applied to this stopped profile gives a model $M$ with $\mathbb{E}_{\pi \sim p} D_H^2(M(\pi), \bar M(\pi)) \le \varepsilon^2$ on which the profile has large regret. Subadditivity of squared Hellinger distance over rounds bounds the Hellinger distance between the laws of the interaction under $M$ and $\bar M$ by a constant, and a change-of-measure inequality for bounded functions transfers the regret from $\bar M$ to $M$.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.5.1 (Eqs. (7.30)–(7.31)) and Section 8.4 (Theorem 8.1).
- D. J. Foster, N. Golowich, Y. Han, "Tight Guarantees for Interactive Decision Making with the Decision-Estimation Coefficient", COLT (2023), PMLR 195, Section 1.3, Eqs. (7)–(9).
