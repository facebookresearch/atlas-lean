# Swap regret under bandit feedback with nearly linear rounds

In the adversarial bandit setting with $N$ actions (the learner observes only the loss of the action it plays), for every $\varepsilon \in (0,1)$ there is an algorithm with expected normalized swap regret at most $\varepsilon$ after

$$
T \ge N\cdot\big(\log(N)/\varepsilon\big)^{O(1/\varepsilon)}
$$

rounds. For constant $\varepsilon$ this is $\tilde O(N)$ rounds, only a polylogarithmic factor more than the full-information non-distributional setting, in contrast with external regret, where bandit and full-information round complexities differ exponentially in $N$.

## Proof sketch

Run TreeSwap with a bandit external-regret learner (such as Exp3) at each level, feeding importance-weighted estimates of block-averaged losses; since each level's learner advances only once per block, the variance of the estimates is controlled by exploring within the block, and the tree lemma applies to the expected losses.

## Depends on

- [Oblivious adversarial bandits](../../reinforcement-learning/multi-armed-bandits/oblivious-adversarial-bandits.md)
- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret.md)

## Proof depends on

- [Swap regret of the path mixture is controlled by external regret of the levels](treeswap-path-mixture-lemma.md)
- [TreeSwap: swap regret from external regret on a tree of restarts](treeswap-algorithm.md)
- [Regret of Exp3 for adversarial bandits](../../reinforcement-learning/multi-armed-bandits/regret-of-exp3-for-adversarial-bandits.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786.
