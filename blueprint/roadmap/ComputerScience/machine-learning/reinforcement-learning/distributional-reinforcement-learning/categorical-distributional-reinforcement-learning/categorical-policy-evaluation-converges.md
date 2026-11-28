# Sample-based categorical policy evaluation converges

Sample-based categorical policy evaluation with mixture updates converges almost surely to the fixed point of the projected categorical operator, in the supremum Cramér metric. Then the stochastic iterates track the deterministic categorical fixed point.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. Run the [categorical evaluation algorithm](../categorical-distributional-reinforcement-learning/categorical-evaluation-with-mixture-updates.md) (evaluation variant) for a policy $\pi$ with $\gamma \in [0,1)$, initial laws supported in $[z_1, z_K]$, and step sizes $\alpha_t(x,a) \in [0,1]$ satisfying the Robbins–Monro conditions, with the sampling and measurability conditions stated there. Then, with $\eta_{\mathcal{C}}$ the [fixed point of the projected categorical operator](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md) and $\bar \ell_2$ the [supremum Cramér metric](../categorical-distributional-reinforcement-learning/cramer-distance.md),

$$\bar \ell_2(\eta_t, \eta_{\mathcal{C}}) \to 0 \quad \text{as } t \to \infty, \text{ almost surely.}$$

## Depends on

- [Sample-based categorical evaluation and Q-learning with mixture updates](../categorical-distributional-reinforcement-learning/categorical-evaluation-with-mixture-updates.md)
- [The projected categorical operator is a √γ-contraction with a unique fixed point](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Proof depends on

- [Averaged projected iterates from the grid endpoints converge monotonically](../categorical-distributional-reinforcement-learning/monotone-averaged-projected-iterates.md)
- [Categorical evaluation iterates are eventually sandwiched between monotone bounds](../categorical-distributional-reinforcement-learning/sandwich-of-categorical-evaluation-iterates.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Expansion

Given $\varepsilon > 0$, choose $k$ with $\bar \ell_2(U_k, \eta_{\mathcal{C}}) < \varepsilon$ and $\bar \ell_2(L_k, \eta_{\mathcal{C}}) < \varepsilon$ ([monotone convergence of the averaged iterates](../categorical-distributional-reinforcement-learning/monotone-averaged-projected-iterates.md)), so $\bar \ell_2(L_k, U_k) < 2\varepsilon$. For $t > T_k$ the [sandwich](../categorical-distributional-reinforcement-learning/sandwich-of-categorical-evaluation-iterates.md) gives $L_k \preceq \eta_t \preceq U_k$, hence $F_{U_k} \le F_{\eta_t} \le F_{L_k}$ pointwise and $\bar \ell_2(\eta_t, L_k) \le \bar \ell_2(U_k, L_k)$. Therefore $\bar \ell_2(\eta_t, \eta_{\mathcal{C}}) \le 2 \bar \ell_2(L_k, U_k) + \bar \ell_2(U_k, \eta_{\mathcal{C}}) < 5\varepsilon$ for all $t > T_k$, almost surely. The hypotheses $\alpha_t \in [0,1]$, adaptedness and conditional sampling are not written in the source's statement, which lists only (i) the Robbins–Monro conditions and (ii) initial support in $[z_1, z_K]$; its proof uses them. No reward moments are needed, because the projection keeps every law in $[z_1, z_K]$. The theorem covers the mixture update, not the Kullback–Leibler gradient update of C51.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.3, Theorem 1, proved in appendix Section 9.
