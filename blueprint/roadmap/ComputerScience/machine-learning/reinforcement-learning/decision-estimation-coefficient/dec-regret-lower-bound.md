# The localized DEC lower bounds the regret of every algorithm

There are absolute constants $c, C > 0$ such that for every model class $\mathcal{M}$ (with rewards in $[0,1]$) and every algorithm, for $T$ large enough,

$$
\sup_{M^\star \in \mathcal{M}} \mathbb{E}^{M^\star}[\mathrm{Reg}_T] \ge c\cdot T\cdot \mathrm{dec}_{\gamma, \varepsilon_\gamma}(\mathcal{M}) \quad \text{with } \gamma = C\sqrt{T}\ \text{and a localization radius } \varepsilon_\gamma \approx \gamma/T,
$$

up to lower-order terms and logarithmic factors. Together with the upper bound, the DEC is necessary and sufficient for sample-efficient interactive decision making, up to the gap between $\mathrm{dec}$ and its localized version and the estimation complexity $\log|\mathcal{M}|$; the approach is a decision-theoretic analogue of Le Cam's two-point method.

## Proof sketch

Fix a reference model $\bar M$ and run the algorithm on it; let $p$ be its average decision distribution. If the algorithm had small regret on every alternative $M$ in the localized class, then by the DEC there is $M$ for which $p$ has large regret on $M$ unless $\mathbb{E}_{\pi \sim p} D_H^2(M(\pi), \bar M(\pi))$ is large. The total Hellinger information collected over $T$ rounds is at most $T$ times this average, so if it is below a constant the laws of the histories under $M$ and $\bar M$ are close in total variation, and the algorithm cannot distinguish them, which yields the bound via Le Cam's lemma.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Le Cam's two-point lower bound](../../../../Probability/statistical-estimation/minimax-lower-bounds/mul-one-sub-total-variation-dist-le-mini.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Le Cam's two-point lower bound](../../../../Probability/statistical-estimation/minimax-lower-bounds/mul-one-sub-total-variation-dist-le-mini.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
