# Optimal contextual bandits from online regression oracles

Consider contextual bandits with $K$ actions, contexts chosen adversarially, and realizable mean rewards $\mathbb{E}[r \mid x, a] = f^\star(x,a)$ for some $f^\star$ in a class $\mathcal{F}$. Given any online regression oracle for $\mathcal{F}$ with square-loss regret $\mathrm{Reg}_{\mathrm{Sq}}(T)$, the **SquareCB** algorithm, which at each round plays the inverse-gap-weighting distribution computed from the oracle's predictions $\hat f_t(x_t, \cdot)$ with $\gamma$ of order $\sqrt{KT/(\mathrm{Reg}_{\mathrm{Sq}}(T) + \log(2/\delta))}$, has, for every $\delta \in (0,1)$, with probability at least $1-\delta$,

$$
\mathrm{Reg}_T \le 4\sqrt{K\,T\,\mathrm{Reg}_{\mathrm{Sq}}(T)} + 8\sqrt{K\,T\log(2/\delta)},
$$

with per-round runtime $O(K\,\mathcal{T}_{\mathrm{Sq}})$ and memory $O(K\,\mathcal{M}_{\mathrm{Sq}})$, where $\mathcal{T}_{\mathrm{Sq}}$ and $\mathcal{M}_{\mathrm{Sq}}$ are the oracle's per-round runtime and maximum memory. For finite classes $\mathrm{Reg}_{\mathrm{Sq}}(T) = O(\log|\mathcal{F}|)$, recovering $O(\sqrt{KT\log|\mathcal{F}|})$. Minimax optimality is shown only in a restricted regime: when contexts and losses are i.i.d. and $\mathcal{F}$ tensorizes as $f(x,a) = g_a(x)$ with each $g_a$ in a base class $\mathcal{G}$ of empirical entropy $O(\varepsilon^{-p})$, a suitable oracle gives $\mathrm{Reg}_T = \tilde O\big((KT)^{\frac{1+p}{2+p}} + \sqrt{K^2 T\log(1/\delta)}\big)$, matching in $T$ the lower bound $\tilde\Omega(T^{\frac{1+p}{2+p}})$ that holds for some such class with $K = 2$.

## Proof sketch

At each round, inverse gap weighting gives instantaneous regret at most $K/\gamma$ plus $\gamma$ times the expected squared error of $\hat f_t$ on the played action (the per-round DEC bound for bandits with the oracle's prediction as reference). Summing, the squared errors are bounded by the oracle's square-loss regret by realizability, giving $TK/\gamma + \gamma\,\mathrm{Reg}_{\mathrm{Sq}}(T)$, optimized at the stated $\gamma$.

## Depends on

- [Contextual bandits with online regression oracles](contextual-bandit-regression-oracle.md)

## Proof depends on

- [DEC of multi-armed and linear bandits via inverse gap weighting](../decision-estimation-coefficient/dec-bandits-inverse-gap-weighting.md)

## Sources

- D. J. Foster, A. Rakhlin, "Beyond UCB: Optimal and Efficient Contextual Bandits with Regression Oracles", ICML (2020), arXiv:2002.04926, Assumptions 1, 2a and 3, Theorems 1, 2 and 3.
