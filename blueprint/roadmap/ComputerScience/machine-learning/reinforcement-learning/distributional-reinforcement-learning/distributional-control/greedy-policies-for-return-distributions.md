# Greedy policies for a return-distribution function

A stochastic policy is greedy for a return-distribution function when, in every state, it puts all its probability on actions whose mean return is largest.

Let $\eta \in \mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ be a [return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md) with mean vector $m(\eta)$. The set of greedy policies for $\eta$ is the set of [stochastic policies](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

$$\mathcal{G}_\eta = \Bigl\{ \pi : \sum_{a \in \mathcal{A}} \pi(a \mid x) \, m(\eta)(x,a) = \max_{a' \in \mathcal{A}} m(\eta)(x,a') \text{ for every } x \in \mathcal{X} \Bigr\}.$$

Equivalently, $\pi \in \mathcal{G}_\eta$ when each $\pi(\cdot \mid x)$ is supported on $\arg\max_{a} m(\eta)(x,a)$. Because $\mathcal{A}$ is finite and nonempty, $\mathcal{G}_\eta$ contains a deterministic policy. When the maximum is attained by several actions at a state, $\mathcal{G}_\eta$ contains every mixture of them there; a tie-breaking rule is a choice of one element of $\mathcal{G}_\eta$.

## Depends on

- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

None.

## Expansion

The definition compares means only: two return-distribution functions with the same mean vector have the same greedy policies, however different their laws. The quantifier "for every $x$" is implicit in Bellemare, Dabney and Munos's display and is written out here. Rowland and coauthors use a deterministic selection $a^*(x') \in \arg\max_{a'} \mathbb{E}_{R \sim \eta^{(x',a')}} R$, which is one element of $\mathcal{G}_\eta$.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.4, Definition 2.
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.3 (the control operator with $a^*(x^\prime) \in \arg\max$).
