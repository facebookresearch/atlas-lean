# Contextual decision processes with low Bellman rank are PAC learnable

If a contextual decision process and a finite class $\mathcal{F}$ admit a Bellman factorization with Bellman rank $M$ and norm parameter $\zeta$, then the **OLIVE** algorithm (optimism-led iterative value-function elimination) returns, with probability at least $1-\delta$, a policy $\hat\pi$ with $V^{\hat\pi} \ge V^*_{\mathcal{F}} - \varepsilon$, where $V^*_{\mathcal{F}}$ is the value of the best greedy policy of a function in $\mathcal{F}$ satisfying all average Bellman equations, using $\tilde O\big(M^2 H^3 K\log(|\mathcal{F}|\zeta/\delta)/\varepsilon^2\big)$ episodes, independent of the number of distinct observations. When the MDP's optimal $Q$-function lies in $\mathcal{F}$ (realizability), $V^*_{\mathcal{F}}$ is the optimal value.

## Proof sketch

OLIVE maintains a version space of value functions consistent with all average Bellman-error constraints tested so far and plays the greedy policy of the most optimistic surviving function. Either that policy is near optimal, or its roll-in reveals a level with large average Bellman error, which eliminates the optimistic function. The low-rank factorization implies that each elimination step reduces an ellipsoid potential in $\mathbb{R}^M$ by a constant factor, so there are at most $O(MH\log(1/\varepsilon))$ elimination rounds.

## Depends on

- [Contextual decision processes and Bellman rank](bellman-rank.md)

## Sources

- N. Jiang, A. Krishnamurthy, A. Agarwal, J. Langford, R. E. Schapire, "Contextual Decision Processes with Low Bellman Rank are PAC-Learnable", ICML (2017), arXiv:1610.09512, Definitions 3 and 4, Facts 1 and 2, Theorem 1 and Lemma 3.
