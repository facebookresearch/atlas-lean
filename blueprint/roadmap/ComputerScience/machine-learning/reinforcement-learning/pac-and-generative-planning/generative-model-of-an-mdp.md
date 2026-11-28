# Generative model of an MDP

A generative model of an MDP is a sampling oracle: given any state-action pair, it returns a next state drawn from that pair's transition distribution, independently of all earlier calls. Its sample cost is the number of calls; the usual scheme calls it the same number of times at every pair.

Let $M = (S, A, P, r, \gamma)$ be a discounted MDP with finite state and action sets, transition probabilities $P(s' \mid s, a)$, rewards $r(s, a)$ and discount $\gamma$.

**Definition.** A generative model (simulator) for $M$ is an oracle that, on input a pair $(s, a) \in S \times A$, returns a state $s' \in S$ drawn from $P(\cdot \mid s, a)$, independently of the outputs of all previous calls. A method that uses it has sample complexity equal to the number of calls it makes.

**Uniform sampling.** For an integer $N \ge 1$, calling the oracle $N$ times at every pair produces states $s^1_{s,a}, \dots, s^N_{s,a}$ for each $(s, a)$, using $N|S||A|$ calls in total. The family $(s^i_{s,a})_{(s,a) \in S \times A,\ 1 \le i \le N}$ is independent, and each $s^i_{s,a}$ has law $P(\cdot \mid s, a)$.

When the rewards are not known in advance, the source definition also returns a reward with each sample; the planning pages of this topic take $r$ known and deterministic, as their sources do. Model-based methods plug the samples into the empirical MDP $\hat M$, which keeps the rewards and the discount of $M$ and replaces each transition row by the empirical frequencies of its $N$ samples, $\hat P(s' \mid s, a) = \frac1N\sum_{i=1}^N \mathbf 1\{s^i_{s,a} = s'\}$; with $N \ge 1$ its rows are probability distributions.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

The generative model removes the exploration problem: samples can be taken at any pair, so the only question is how many to take. Unknown or random rewards add only a lower-order number of samples, which is why the sources take the reward as known. A restricted, non-minimax accuracy bound for uniform sampling, through an $\ell_1$ estimate of each empirical row and the simulation lemma, is the [generative-model sample bound](../sample-complexity-and-exploration/generative-model-sample-bound.md).

## Sources

- S. M. Kakade, *On the Sample Complexity of Reinforcement Learning*, PhD thesis, University College London, 2003, [homes.cs.washington.edu](https://homes.cs.washington.edu/~sham/papers/thesis/sham_thesis.pdf): Section 2.4 (sampling models; sample complexity as the number of calls to the sampling model) and Definition 2.4.1 (generative model, introduced by Kearns, Mansour and Ng, 1999).
- M. G. Azar, R. Munos and H. J. Kappen, "Minimax PAC bounds on the sample complexity of reinforcement learning with a generative model", *Machine Learning* 91 (2013), 325–349, doi:10.1007/s10994-013-5368-1: Section 2.1 and Algorithm 3 ($n$ calls per pair, $T = nN$ calls in total; pp. 329–330).
- G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, "Breaking the Sample Size Barrier in Model-Based Reinforcement Learning with a Generative Model", *Advances in Neural Information Processing Systems* 33 (NeurIPS 2020), [proceedings.neurips.cc](https://proceedings.neurips.cc/paper/2020/hash/96ea64f3a1aa2fd00c72faacf0cb8ac9-Abstract.html): Section 2, paragraph "A generative model and an empirical MDP" ($N$ independent samples per pair, $N|S||A|$ in total).
- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): Section 2, paragraph "Generative Model".
