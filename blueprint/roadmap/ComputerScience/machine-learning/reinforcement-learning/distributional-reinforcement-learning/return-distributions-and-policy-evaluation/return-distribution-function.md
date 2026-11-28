# Return-distribution function

A return-distribution function assigns a probability law on the real line to every state–action pair. Distributional Bellman operators act on these families of laws, not on random variables.

For finite $\mathcal{X}$ and $\mathcal{A}$, a *return-distribution function* is a family $\eta = (\eta^{(x,a)})_{(x,a) \in \mathcal{X} \times \mathcal{A}}$ of Borel probability measures on $\mathbb{R}$; the set of them is $\mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$. For $1 \le q < \infty$, $\mathscr{P}_q(\mathbb{R})$ denotes the probability measures $\nu$ with $\int |t|^q \, \nu(dt) < \infty$, and $\mathscr{P}_q(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ the return-distribution functions all of whose components lie in $\mathscr{P}_q(\mathbb{R})$. For $\eta \in \mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ the mean vector $m(\eta) \in \mathbb{R}^{\mathcal{X} \times \mathcal{A}}$ is

$$m(\eta)(x,a) = \int_{\mathbb{R}} t \, \eta^{(x,a)}(dt).$$

The cumulative distribution function of a component is $F_{\eta^{(x,a)}}(t) = \eta^{(x,a)}((-\infty, t])$.

Bellemare, Dabney and Munos call such an object a value distribution and write it as a random vector $Z(x,a)$; a statement about $Z$ is a statement about the laws $\eta^{(x,a)}$ of its components, and a distributional equation $U \overset{D}{=} V$ asserts that $U$ and $V$ have the same law. Their space of "value distributions with bounded moments" is not specified further; each page of this topic names the moment class it needs.

## Depends on

- [Probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

Rowland and coauthors introduce the name "return distribution function" to stress that the object is a function from state–action pairs to probability measures, and state their results in terms of the measures themselves. Writing statements about laws avoids conflating random variables defined on different probability spaces, which Bellemare, Dabney and Munos do on purpose for legibility (Section 3.2).

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.2, eq. (2) and the name "return distribution function".
- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3 (value distributions), Section 3.1 (distributional equations) and Section 3.2 (the space of value distributions with bounded moments).
