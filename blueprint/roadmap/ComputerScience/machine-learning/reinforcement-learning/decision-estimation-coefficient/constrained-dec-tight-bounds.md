# Constrained DEC gives tight expected-regret bounds with improper reference models

Let $\mathrm{dec}^c_\varepsilon(\mathcal{M}, \bar M)$ be the constrained DEC and $\mathrm{dec}^c_\varepsilon(\mathcal{M}) = \sup_{\bar M \in \mathrm{co}(\mathcal{M})} \mathrm{dec}^c_\varepsilon(\mathcal{M} \cup \{\bar M\}, \bar M)$, for a model class $\mathcal{M}$ with rewards in $[0,1]$ that contains the true model. Let $V(\mathcal{M}) \ge e$ bound the density ratios $M'(E \mid \pi)/M(E \mid \pi)$ over $M, M' \in \mathcal{M}$, decisions $\pi$ and events $E$, and let $\mathcal{M}^+ \supseteq \mathrm{co}(\mathcal{M})$ be the set of all models with rewards in $[0,1]$ whose density ratios relative to every $M \in \mathcal{M}$ are bounded by $V(\mathcal{M})$.

**Lower bound.** There are absolute constants $c, c', C, C' > 0$ such that, with $C(T) = \log(T \wedge V(\mathcal{M}))$ and $\varepsilon(T) = c/\sqrt{T\,C(T)}$, for every $T$ satisfying the regime condition $\mathrm{dec}^c_{\varepsilon(T)}(\mathcal{M}) \ge C\,\varepsilon(T)$, every algorithm has, under some model in $\mathcal{M}$,

$$
\mathbb{E}[\mathrm{Reg}_T] \ge c'\,\frac{T}{\log T}\,\sup_{\bar M \in \mathcal{M}^+} \mathrm{dec}^c_{\varepsilon(T)}\big(\mathcal{M} \cup \{\bar M\}, \bar M\big) - C'\,\frac{\sqrt{T}}{\log T} \ge c'\,\frac{T}{\log T}\,\mathrm{dec}^c_{\varepsilon(T)}(\mathcal{M}) - C'\,\frac{\sqrt{T}}{\log T}.
$$

**Upper bound.** Suppose $\mathcal{M}$ is finite and the coefficient satisfies the growth condition $\mathrm{dec}^c_\varepsilon(\mathcal{M}) \le C_{\mathrm{reg}}^2\,\mathrm{dec}^c_{\varepsilon/C_{\mathrm{reg}}}(\mathcal{M})$ for all $\varepsilon \in (0, 2)$ and some constant $C_{\mathrm{reg}} > 1$. Then for every $\delta \in (0,1)$ there is an algorithm (a constrained version of E2D) such that, with probability at least $1 - \delta$,

$$
\mathrm{Reg}_T \le O(T\log T)\cdot\mathrm{dec}^c_{\bar\varepsilon(T)}(\mathcal{M}) + O\Big(\sqrt{T\log(1/\delta)\log(|\mathcal{M}|/\delta)}\Big), \qquad \bar\varepsilon(T) = C''\sqrt{\frac{\log(|\mathcal{M}|/\delta)\log(1/\delta)}{T}},
$$

with a numerical constant $C''$ and constants in $O(\cdot)$ depending only on $C_{\mathrm{reg}}$.

The two bounds use reference models in $\mathcal{M}^+ \supseteq \mathrm{co}(\mathcal{M})$ and in $\mathrm{co}(\mathcal{M})$ respectively, and differ in radius by the estimation factor. The lower bound needs no localization and holds for every algorithm; since it holds with improper reference models $\bar M \in \mathrm{co}(\mathcal{M})$ and not only $\bar M \in \mathcal{M}$, such reference models are not an artifact of the upper bound.

## Proof sketch

The lower bound first proves the analogous bound with proper reference models $\bar M \in \mathcal{M}$ by a change-of-measure argument under $\bar M$, and then extends it to an arbitrary $\bar M \in \mathcal{M}^+$ by showing that an algorithm with regret $R$ on $\mathcal{M}$ yields one with regret $O(R\log T)$ on $\mathcal{M} \cup \{\bar M\}$. The upper bound runs E2D with the constrained min-max problem over epochs of doubling length; the estimation oracle is restricted to a confidence set of models carried over from the previous epoch, and a Hellinger test on a few sampled rounds keeps the true model in that set.

## Depends on

- [Decision making with structured observations](decision-making-structured-observations.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)
- [The constrained DEC lower bounds the regret of every algorithm](dec-regret-lower-bound.md)

## Proof depends on

- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](e2d-regret-upper-bound.md)

## Sources

- D. J. Foster, N. Golowich, Y. Han, "Tight Guarantees for Interactive Decision Making with the Decision-Estimation Coefficient", COLT (2023), PMLR 195, Eqs. (7)–(9), Appendix C.1 (Theorem C.1, Eqs. (15)–(16)) and Appendix C.2 (Theorem C.2, Assumptions C.1 and C.2); in the arXiv version arXiv:2301.08215, Theorem 2.2 (Eqs. (15)–(16)), Assumption 3.3 and Theorem 3.2.
- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.5 (Proposition 7.2).
