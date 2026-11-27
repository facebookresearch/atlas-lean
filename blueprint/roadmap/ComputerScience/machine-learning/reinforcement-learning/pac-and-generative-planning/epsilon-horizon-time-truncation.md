# Epsilon-horizon time truncation

In a discounted MDP with payoffs in $[0, R_{\max}]$, the expected discounted return of any policy over the first $T \ge (1/(1-\gamma))\log(R_{\max}/(\varepsilon(1-\gamma)))$ steps is within $\varepsilon$ below its infinite-horizon return. This $T$ is the $\varepsilon$-horizon time.

**Lemma.** Let $M$ be a Markov decision process whose payoff at each state $i$ has mean $R_M(i)$ with $0 \le R_M(i) \le R_{\max}$, let $0 \le \gamma < 1$ and $\varepsilon > 0$, and let $\pi$ be any policy in $M$. For a path visiting states $i_1, i_2, \dots$ write $V_M(p) = R_M(i_1) + \gamma R_M(i_2) + \dots + \gamma^{T-1} R_M(i_T)$ for the discounted return of its first $T$ steps, $V^\pi_M(i, T)$ for the expectation of this quantity over the paths of $\pi$ started at $i$, and $V^\pi_M(i) = \lim_{T \to \infty} V^\pi_M(i, T)$. If

$$T \ge \frac{1}{1-\gamma}\log\Big(\frac{R_{\max}}{\varepsilon(1-\gamma)}\Big),$$

then for every state $i$

$$V^\pi_M(i, T) \le V^\pi_M(i) \le V^\pi_M(i, T) + \varepsilon.$$

The right-hand side of the condition on $T$ is called the $\varepsilon$-horizon time of $M$.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

The lower bound holds because the payoff means are nonnegative. For the upper bound, fix an infinite path with expected payoffs $R_1, R_2, \dots$; the discounted tail after step $T$ is at most $R_{\max}\gamma^T \sum_{k \ge 0}\gamma^k = R_{\max}\gamma^T/(1-\gamma)$. Reading $\log$ as the natural logarithm, $\gamma^T \le e^{-(1-\gamma)T}$ shows that the stated $T$ makes this at most $\varepsilon$, and averaging the pathwise bound over the path distribution of $\pi$ gives the claim. When $R_{\max} \le \varepsilon(1-\gamma)$ the bound on $T$ is vacuous and every $T \ge 0$ works. The PAC-MDP analyses use the same truncation with $R_{\max} = 1$, that is $H = (1/(1-\gamma))\ln(1/(\varepsilon(1-\gamma)))$.

## Sources

- M. Kearns and S. Singh, "Near-Optimal Reinforcement Learning in Polynomial Time", *Machine Learning* 49 (2002), 209–232, doi:10.1023/A:1017984413808: Lemma 2 and equations (9)–(14) (Section 4, pp. 215–216).
- A. L. Strehl, L. Li and M. L. Littman, "Reinforcement Learning in Finite MDPs: PAC Analysis", *Journal of Machine Learning Research* 10 (2009), 2413–2444, [jmlr.org](https://jmlr.org/papers/volume10/strehl09a/strehl09a.pdf): proof of Theorem 10 (p. 2428), which applies this lemma with unit payoff bound.
