# Swap regret of the path mixture is controlled by external regret of the levels

In online learning with $N$ actions (or a hypothesis class $F$), at each round $t = 1, \dots, T$ the learner chooses a distribution $p_t$ over actions and an adversary chooses a loss vector $\ell_t \in [0,1]^N$. The **(normalized, distributional) swap regret** is

$$
\mathrm{SwapReg}_T = \frac{1}{T}\max_{\phi : [N] \to [N]} \sum_{t=1}^T \sum_{a} p_t(a)\big(\ell_t(a) - \ell_t(\phi(a))\big),
$$

and the learner achieves **$\varepsilon$-swap regret** after $T$ rounds if $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon$ against every adaptive adversary. In the non-distributional variant the learner must play a sampled action rather than a distribution. Suppose $\mathcal{A}$ guarantees average external regret at most $\varepsilon$ over any $M$ consecutive (block-averaged) loss vectors. Then TreeSwap satisfies $\mathbb{E}[\mathrm{SwapReg}_T] \le \varepsilon + 1/d$ after $T = M^d$ rounds. The bound depends on the external-regret guarantee only, not on the number of actions, and therefore holds for arbitrary (possibly infinite) action sets and hypothesis classes whenever a no-external-regret learner exists.

## Proof sketch

Fix a swap function $\phi$. Decompose the rounds into the nested blocks of the tree; on a block of level $k$, the instance at level $k$ plays a fixed distribution on each of its $M$ sub-blocks and has external regret at most $\varepsilon$ against every fixed comparator over those sub-blocks. Within a sub-block, the mixture $p_t$ changes only through the deeper levels, and a telescoping argument across levels shows that the swap deviation $\phi$ applied to the mixture can be charged to the external regret of each level against the comparator $\phi$ applied to that level's frozen distribution, except for one level out of $d$ whose distribution is not yet frozen, which contributes at most $1/d$.

## Depends on

- [TreeSwap: swap regret from external regret on a tree of restarts](treeswap-algorithm.md)
- [External regret is at most swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret-le-swap-regret.md)

## Proof depends on

- [TreeSwap: swap regret from external regret on a tree of restarts](treeswap-algorithm.md)
- [External regret is at most swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret-le-swap-regret.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786.
