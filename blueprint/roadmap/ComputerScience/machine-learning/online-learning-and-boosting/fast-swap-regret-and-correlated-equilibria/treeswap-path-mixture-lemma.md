# Swap regret of the path mixture is controlled by external regret of the levels

In online learning with $N$ actions (or a hypothesis class $F$), at each round $t = 1, \dots, T$ the learner chooses a distribution $p_t$ over actions and an adversary chooses a loss vector $\ell_t \in [0,1]^N$. The **(normalized, distributional) swap regret** is

$$
\mathrm{SwapReg}_T = \frac{1}{T}\max_{\phi : [N] \to [N]} \sum_{t=1}^T \sum_{a} p_t(a)\big(\ell_t(a) - \ell_t(\phi(a))\big),
$$

and the learner achieves **$\varepsilon$-swap regret** after $T$ rounds if $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon$ against every adaptive adversary. In the non-distributional variant the learner must play a sampled action rather than a distribution. Let the losses range over a class closed under convex combinations (so that block averages are again admissible losses), and suppose $\mathcal{A}$, run for $M$ rounds against an adaptive adversary, guarantees normalized external regret at most $\varepsilon$. Then for $M \ge 2$ and $M^{d-1} \le T \le M^d$, TreeSwap satisfies $\mathrm{SwapReg}_T \le \varepsilon + 3/d$. The bound depends on the external-regret guarantee only, not on the number of actions, and therefore holds for arbitrary (possibly infinite) action sets and hypothesis classes whenever a no-external-regret learner exists.

## Proof sketch

Fix a swap function $\phi$. Decompose the rounds into the nested blocks of the tree; on a block of level $k$, the instance at level $k$ plays a fixed distribution on each of its $M$ sub-blocks and has external regret at most $\varepsilon$ against every fixed comparator over those sub-blocks. Within a sub-block, the mixture $p_t$ changes only through the deeper levels, and a telescoping argument across levels shows that the swap deviation $\phi$ applied to the mixture can be charged to the external regret of each level against the comparator $\phi$ applied to that level's frozen distribution, up to boundary terms from the levels whose distributions are not yet frozen and from a horizon $T$ that is not a power of $M$, which contribute at most $3/d$ in total.

## Depends on

- [TreeSwap: swap regret from external regret on a tree of restarts](treeswap-algorithm.md)
- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786, Theorem 3.1.
