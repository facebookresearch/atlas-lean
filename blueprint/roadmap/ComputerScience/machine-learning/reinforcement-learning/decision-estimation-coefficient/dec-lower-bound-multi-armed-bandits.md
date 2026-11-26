# The DEC lower bound recovers the square-root lower bound for multi-armed bandits

For the class of $K$-armed bandits with Gaussian rewards of unit variance and means in $[0,1]$, $\mathrm{dec}_{\gamma}(\mathcal{M}) \ge c\,K/\gamma$ for all $\gamma \ge C K$, and the localized version satisfies the same bound with radius $\varepsilon_\gamma \approx \gamma/T$. Plugging into the DEC lower bound with $\gamma \asymp \sqrt{KT}$ gives the minimax lower bound $\Omega(\sqrt{KT})$ on the regret, matching the inverse-gap-weighting upper bound up to the estimation term.

## Proof sketch

Take the reference model with all means equal to $\tfrac12$ and alternatives raising one arm's mean by $\Delta = K/\gamma$. For any decision distribution $p$, some arm $a$ has $p(a) \le 1/K$; on the alternative boosting $a$, the regret of $p$ is at least $\Delta(1 - 1/K)$ while the Hellinger penalty is $\gamma\,p(a)\,O(\Delta^2) \le O(\gamma\Delta^2/K) = O(K/\gamma)$ with a small constant, leaving $\Omega(K/\gamma)$.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Stochastic k-armed bandits: canonical history law and regret](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)

## Proof depends on

- [The localized DEC lower bounds the regret of every algorithm](dec-regret-lower-bound.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
