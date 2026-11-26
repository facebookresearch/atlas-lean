# Contextual decision processes with low Bellman rank are PAC learnable

If $\mathcal{F}$ contains the optimal value function (realizability) and the contextual decision process has Bellman rank $M$, then the **OLIVE** algorithm (optimism-led iterative value-function elimination) outputs an $\varepsilon$-optimal policy with probability at least $1-\delta$ using a number of episodes polynomial in $M$, $K$, $H$, $1/\varepsilon$ and $\log(|\mathcal{F}|/\delta)$, namely $\tilde O\big(M^2 H^3 K\log(|\mathcal{F}|/\delta)/\varepsilon^2\big)$, independent of the number of distinct observations.

## Proof sketch

OLIVE maintains a version space of value functions consistent with all average Bellman-error constraints tested so far and plays the greedy policy of the most optimistic surviving function. Either that policy is near optimal, or its roll-in reveals a level with large average Bellman error, which eliminates the optimistic function. The low-rank factorization implies that each elimination step reduces an ellipsoid potential in $\mathbb{R}^M$ by a constant factor, so there are at most $O(MH\log(1/\varepsilon))$ elimination rounds.

## Depends on

- [Contextual decision processes and Bellman rank](bellman-rank.md)

## Sources

- N. Jiang, A. Krishnamurthy, A. Agarwal, J. Langford, R. E. Schapire, "Contextual Decision Processes with Low Bellman Rank are PAC-Learnable", ICML (2017), arXiv:1610.09512.
