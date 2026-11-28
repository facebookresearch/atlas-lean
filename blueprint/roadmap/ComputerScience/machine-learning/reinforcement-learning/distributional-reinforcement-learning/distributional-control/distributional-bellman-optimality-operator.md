# Distributional Bellman optimality operator

A distributional Bellman optimality operator applies to each return-distribution function the distributional Bellman operator of some policy that is greedy for it. Different greedy selection rules give different operators.

Let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) with $M_1 < \infty$ and $\gamma \in [0,1)$. A *greedy selection rule* assigns to each $\eta \in \mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ a policy $\pi_\eta \in \mathcal{G}_\eta$, a [greedy policy](../distributional-control/greedy-policies-for-return-distributions.md) for $\eta$; the rule may depend on all of $\eta$, not only on its means. The *distributional Bellman optimality operator* of the rule is

$$\mathcal{T} \eta = \mathcal{T}^{\pi_\eta} \eta, \qquad \eta \in \mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}},$$

with $\mathcal{T}^{\pi}$ the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md). Every such $\mathcal{T}$ maps $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ into itself, and its iterates are $\eta_{k+1} = \mathcal{T} \eta_k$. Statements about "the" optimality operator below quantify explicitly over selection rules.

## Depends on

- [Greedy policies for a return-distribution function](../distributional-control/greedy-policies-for-return-distributions.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)

## Expansion

$\mathcal{T}\eta$ lies in $\mathscr{P}_1$ because $\mathcal{T}^{\pi_\eta}$ preserves first moments when $M_1 < \infty$. Bellemare, Dabney and Munos call any operator implementing a greedy selection rule a distributional Bellman optimality operator; Rowland and coauthors' control operator, with a deterministic $a^*(x')$ in the argmax, is one of them. Bellemare, Dabney and Munos also define the optimal value distributions as the return distributions of optimal policies (Definition 1); that set plays no role in the statements of this topic.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.4, the definition of a distributional Bellman optimality operator after Definition 2, and Definition 1.
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.3, the control operator and eq. (5).
