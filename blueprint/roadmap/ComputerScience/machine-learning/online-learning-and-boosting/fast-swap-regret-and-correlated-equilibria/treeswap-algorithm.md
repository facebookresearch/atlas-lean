# TreeSwap: swap regret from external regret on a tree of restarts

In online learning with $N$ actions (or a hypothesis class $F$), at each round $t = 1, \dots, T$ the learner chooses a distribution $p_t$ over actions and an adversary chooses a loss vector $\ell_t \in [0,1]^N$. The **(normalized, distributional) swap regret** is

$$
\mathrm{SwapReg}_T = \frac{1}{T}\max_{\phi : [N] \to [N]} \sum_{t=1}^T \sum_{a} p_t(a)\big(\ell_t(a) - \ell_t(\phi(a))\big),
$$

and the learner achieves **$\varepsilon$-swap regret** after $T$ rounds if $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon$ against every adaptive adversary. In the non-distributional variant the learner must play a sampled action rather than a distribution. Given an external-regret algorithm $\mathcal{A}$ for a loss class closed under convex combinations and parameters $M, d \in \mathbb{N}$, **TreeSwap** runs for $T \le M^d$ rounds, indexes round $t$ by the base-$M$ expansion $(\sigma_1, \dots, \sigma_d) \in \{0, \dots, M-1\}^d$ of $t - 1$, padded with leading zeros to exactly $d$ digits (so rounds $1, \dots, M^d$ correspond to $(0,\dots,0), \dots, (M-1,\dots,M-1)$), and maintains for each level $k \le d$ an instance of $\mathcal{A}$ that is restarted every $M^{d-k+1}$ rounds and advanced once every $M^{d-k}$ rounds, being fed the average loss of the corresponding block of rounds. At round $t$ the learner plays the uniform mixture $p_t = \frac{1}{d}\sum_{k=1}^d q^{(k)}_t$ of the current outputs $q^{(k)}_t$ of the $d$ active instances along the root-to-leaf path of $t$ in the $M$-ary tree of depth $d$.

## Depends on

- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786, Algorithm 1.
- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC (2024), arXiv:2310.19647.
