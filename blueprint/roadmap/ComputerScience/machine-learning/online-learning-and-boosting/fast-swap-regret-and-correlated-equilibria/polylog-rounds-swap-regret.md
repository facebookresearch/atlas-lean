# Swap regret polylogarithmic in the number of actions

In online learning with $N$ actions (or a hypothesis class $F$), at each round $t = 1, \dots, T$ the learner chooses a distribution $p_t$ over actions and an adversary chooses a loss vector $\ell_t \in [0,1]^N$. The **(normalized, distributional) swap regret** is

$$
\mathrm{SwapReg}_T = \frac{1}{T}\max_{\phi : [N] \to [N]} \sum_{t=1}^T \sum_{a} p_t(a)\big(\ell_t(a) - \ell_t(\phi(a))\big),
$$

and the learner achieves **$\varepsilon$-swap regret** after $T$ rounds if $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon$ against every adaptive adversary. In the non-distributional variant the learner must play a sampled action rather than a distribution. For every $N$ and $\varepsilon \in (0,1)$ there is an algorithm with $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon$ against every adaptive adversary as soon as

$$
T \ge \big(\log(N)/\varepsilon^2\big)^{O(1/\varepsilon)},
$$

with amortized per-round running time $O(N)$ and space $O(N/\varepsilon)$ (TreeSwap with multiplicative weights, $M = O(\log N/\varepsilon^2)$ and $d = O(1/\varepsilon)$). Independently, a multi-scale multiplicative-weights algorithm achieves $\varepsilon$-swap regret after $(\log(N)/\varepsilon)^{O(1/\varepsilon)}$ rounds. For constant $\varepsilon$ this is an exponential improvement in $N$ over the $O(N\log N/\varepsilon^2)$ rounds of the Blum–Mansour reduction; $\Omega(N/\varepsilon^2)$ rounds are necessary in the non-distributional setting, so the improvement requires playing distributions. This resolves the main open problem of Blum and Mansour.

## Proof sketch

Multiplicative weights has average external regret at most $\varepsilon/2$ after $M = O(\log N/\varepsilon^2)$ rounds; the tree lemma with $d = \lceil 6/\varepsilon\rceil$ levels gives swap regret at most $\varepsilon/2 + 3/d \le \varepsilon$ once $T \ge M^{d-1}$. The multi-scale algorithm runs $2^S$ threads of multiplicative weights with $S = \log_2(1/\varepsilon) + 1$ and block size $H = \Theta(\log N/\varepsilon^2)$, thread $k$ treating $H^{k-1}$ days as one meta-day, and plays a uniform mixture of the threads, with an analogous telescoping analysis.

## Depends on

- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [TreeSwap: swap regret from external regret on a tree of restarts](treeswap-algorithm.md)
- [Multi-scale multiplicative weights for swap regret](multiscale-multiplicative-weights.md)

## Proof depends on

- [Swap regret of the path mixture is controlled by external regret of the levels](treeswap-path-mixture-lemma.md)
- [The $\sqrt{T}$ regret bound of Hedge](../hedge-algorithm/regret-le-two-sqrt.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786, Corollary 3.2.
- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC (2024), arXiv:2310.19647, Theorem 1.1 and Algorithm 2.
- A. Blum, Y. Mansour, "From External to Internal Regret", Journal of Machine Learning Research 8 (2007).
