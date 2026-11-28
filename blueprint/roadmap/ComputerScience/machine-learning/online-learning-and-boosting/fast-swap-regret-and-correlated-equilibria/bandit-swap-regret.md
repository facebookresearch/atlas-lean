# Swap regret under bandit feedback with nearly linear rounds

In the adversarial bandit setting with $N$ actions, against a fixed sequence of loss vectors in $[0,1]^N$ (an oblivious adversary), where the learner plays an action and observes only its loss, for every $\varepsilon \in (0,1)$ there is an algorithm with expected normalized swap regret (of the played actions) at most $\varepsilon$ after

$$
T \ge N\cdot\big(\log(N)/\varepsilon\big)^{O(1/\varepsilon)}
$$

rounds. For constant $\varepsilon$ this is $\tilde O(N)$ rounds, only a polylogarithmic factor more than the full-information non-distributional setting, in contrast with external regret, where full information needs $O(\log N)$ rounds and bandit feedback $\Omega(N)$.

## Proof sketch

BanditTreeSwap places at every node of the $M$-ary tree a bandit external-regret learner, a multi-sample variant of Exp3: during each of its $M$ rounds it fixes a distribution, and the actions played within the corresponding block are drawn from mixtures that include it, yielding several importance-weighted samples of its block-averaged loss. Since each learner advances only once per block, its loss estimates average many samples, which controls their variance; the analysis then follows the tree argument for the expected losses.

## Depends on

- [Oblivious adversarial bandits](../../reinforcement-learning/multi-armed-bandits/oblivious-adversarial-bandits.md)
- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret.md)

## Proof depends on

- [Swap regret of the path mixture is controlled by external regret of the levels](treeswap-path-mixture-lemma.md)
- [TreeSwap: swap regret from external regret on a tree of restarts](treeswap-algorithm.md)
- [Regret of Exp3 for adversarial bandits](../../reinforcement-learning/multi-armed-bandits/regret-of-exp3-for-adversarial-bandits.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786, Theorem 3.12 and Algorithm 4.
