# Optimal contextual bandits from online regression oracles

Consider contextual bandits with $K$ actions, contexts chosen adversarially, and realizable mean rewards $\mathbb{E}[r \mid x, a] = f^\star(x,a)$ for some $f^\star$ in a class $\mathcal{F}$. Given any online regression oracle for $\mathcal{F}$ with square-loss regret $\mathrm{Reg}_{\mathrm{Sq}}(T)$, the **SquareCB** algorithm, which at each round plays the inverse-gap-weighting distribution computed from the oracle's predictions $\hat f_t(x_t, \cdot)$ with $\gamma$ of order $\sqrt{KT/(\mathrm{Reg}_{\mathrm{Sq}}(T) + \log(2/\delta))}$, has, for every $\delta > 0$, with probability at least $1-\delta$,

$$
\mathrm{Reg}_T \le 4\sqrt{K\,T\,\mathrm{Reg}_{\mathrm{Sq}}(T)} + 8\sqrt{K\,T\log(2/\delta)},
$$

with per-round runtime and memory those of the oracle plus $O(K)$. For finite classes $\mathrm{Reg}_{\mathrm{Sq}}(T) = O(\log|\mathcal{F}|)$, recovering $O(\sqrt{KT\log|\mathcal{F}|})$, and with i.i.d. contexts the reduction is minimax optimal for general (possibly nonparametric) classes when the oracle attains the optimal regression rate.

## Proof sketch

At each round, inverse gap weighting gives instantaneous regret at most $K/\gamma$ plus $\gamma$ times the expected squared error of $\hat f_t$ on the played action (the per-round DEC bound for bandits with the oracle's prediction as reference). Summing, the squared errors are bounded by the oracle's square-loss regret by realizability, giving $TK/\gamma + \gamma\,\mathrm{Reg}_{\mathrm{Sq}}(T)$, optimized at the stated $\gamma$.

## Depends on

- [Contextual bandits with online regression oracles](contextual-bandit-regression-oracle.md)

## Proof depends on

- [DEC of multi-armed and linear bandits via inverse gap weighting](../decision-estimation-coefficient/dec-bandits-inverse-gap-weighting.md)

## Sources

- D. J. Foster, A. Rakhlin, "Beyond UCB: Optimal and Efficient Contextual Bandits with Regression Oracles", ICML (2020), arXiv:2002.04926, Assumptions 1 and 2a, Theorems 1, 2 and 3.
