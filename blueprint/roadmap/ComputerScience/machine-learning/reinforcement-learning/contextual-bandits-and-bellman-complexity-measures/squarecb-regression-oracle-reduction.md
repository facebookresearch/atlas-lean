# Optimal contextual bandits from online regression oracles

Consider contextual bandits with $K$ actions, contexts chosen adversarially, and realizable mean rewards $\mathbb{E}[r \mid x, a] = f^\star(x,a)$ for some $f^\star$ in a class $\mathcal{F}$. Given any online regression oracle for $\mathcal{F}$ with square-loss regret $\mathrm{Reg}_{\mathrm{Sq}}(T)$, the **SquareCB** algorithm, which at each round plays the inverse-gap-weighting distribution computed from the oracle's predictions $\hat f_t(x_t, \cdot)$ with $\gamma \approx \sqrt{KT/\mathrm{Reg}_{\mathrm{Sq}}(T)}$, has regret

$$
\mathbb{E}[\mathrm{Reg}_T] \le O\big(\sqrt{K\,T\,\mathrm{Reg}_{\mathrm{Sq}}(T)}\big),
$$

with runtime and memory equal to those of the oracle. For finite classes $\mathrm{Reg}_{\mathrm{Sq}}(T) = O(\log|\mathcal{F}|)$, recovering $O(\sqrt{KT\log|\mathcal{F}|})$, and the reduction is minimax optimal for general (possibly nonparametric) classes whenever the oracle attains the optimal regression rate.

## Proof sketch

At each round, inverse gap weighting gives instantaneous regret at most $K/\gamma$ plus $\gamma$ times the expected squared error of $\hat f_t$ on the played action (the per-round DEC bound for bandits with the oracle's prediction as reference). Summing, the squared errors are bounded by the oracle's square-loss regret by realizability, giving $TK/\gamma + \gamma\,\mathrm{Reg}_{\mathrm{Sq}}(T)$, optimized at the stated $\gamma$.

## Depends on

- [Contextual bandits with online regression oracles](contextual-bandit-regression-oracle.md)

## Proof depends on

- [DEC of multi-armed and linear bandits via inverse gap weighting](../decision-estimation-coefficient/dec-bandits-inverse-gap-weighting.md)
- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](../decision-estimation-coefficient/e2d-regret-upper-bound.md)

## Sources

- D. J. Foster, A. Rakhlin, "Beyond UCB: Optimal and Efficient Contextual Bandits with Regression Oracles", ICML (2020), arXiv:2002.04926.
