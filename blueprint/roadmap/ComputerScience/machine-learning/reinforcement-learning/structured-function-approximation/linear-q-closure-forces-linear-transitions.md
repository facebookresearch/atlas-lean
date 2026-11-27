# Bellman closure of linear Q-functions forces linear transitions

If the class of linear action-value functions is mapped into itself by the Bellman operator of every policy, and each state has two actions with different features, then on a finite state space the transition kernel is linear in the features. Realizability of a single value function does not give this.

**Statement.** Fix an episodic MDP with finite state space $\mathcal{S}$, finite action set $\mathcal{A}$, a step $h$, deterministic rewards $r_h : \mathcal{S}\times\mathcal{A} \to [0,1]$ and transition kernel $\mathbb{P}_h$, and a feature map $\phi : \mathcal{S} \times \mathcal{A} \to \mathbb{R}^d$. Let $\mathcal{Q} = \{ (x,a) \mapsto \phi(x,a)^{\mathsf T} w : w \in \mathbb{R}^d \}$. For a policy $\pi : \mathcal{S} \to \mathcal{A}$ and $Q : \mathcal{S} \times \mathcal{A} \to \mathbb{R}$ let

$$
(\mathbb{T}^\pi_h Q)(x,a) = r_h(x,a) + \mathbb{E}_{x' \sim \mathbb{P}_h(\cdot \mid x,a)}\big[Q(x', \pi(x'))\big].
$$

Assume that for every $x \in \mathcal{S}$ there are actions $a, \bar a$ with $\phi(x,a) \ne \phi(x,\bar a)$. If $\mathbb{T}^\pi_h \mathcal{Q} \subseteq \mathcal{Q}$ for every policy $\pi$, then there are vectors $\mu_h(x') \in \mathbb{R}^d$, $x' \in \mathcal{S}$, with

$$
\mathbb{P}_h(x' \mid x, a) = \langle \phi(x,a), \mu_h(x') \rangle \quad \text{for all } x, x' \in \mathcal{S},\ a \in \mathcal{A},
$$

that is, the transition kernel at step $h$ factors through the features as in a [linear MDP](linear-mdp.md). The conclusion is this factorization only; it makes no claim about the normalization of $\mu_h$ or the reward.

The hypothesis quantifies over all policies. It is a completeness condition on the whole linear class, much stronger than linear realizability of $Q^\star$ alone.

## Depends on

- [Expectation under a probability mass function](../../../../Probability/distributions/discrete/expectation-under-a-probability-mass-function/expect.md)

## Proof depends on

None.

## Expansion

Fix $x_0 \in \mathcal{S}$ and actions $a_0, \bar a_0$ with $\phi(x_0,a_0) \ne \phi(x_0, \bar a_0)$, and choose $w_0$ with $w_0^{\mathsf T}(\phi(x_0,a_0) - \phi(x_0,\bar a_0)) = 1$. Let $Q_0 = \phi^{\mathsf T} w_0$ and let $\pi_1, \pi_2$ agree off $x_0$ with $\pi_1(x_0) = a_0$, $\pi_2(x_0) = \bar a_0$. Then $\mathbb{T}^{\pi_1}_h Q_0 - \mathbb{T}^{\pi_2}_h Q_0 = \mathbb{P}_h(x_0 \mid \cdot, \cdot)$, a difference of two members of the linear space $\mathcal{Q}$, so $\mathbb{P}_h(x_0 \mid \cdot,\cdot) = \phi^{\mathsf T} \mu_h(x_0)$ for some vector $\mu_h(x_0)$. Doing this for each $x_0$ gives the claim.

## Sources

- C. Jin, Z. Yang, Z. Wang and M. I. Jordan, "Provably Efficient Reinforcement Learning with Linear Function Approximation", Conference on Learning Theory (COLT 2020), PMLR 125; journal version Mathematics of Operations Research 48(3):1496–1521, 2023, doi:10.1287/moor.2022.1309. Numbers from arXiv:1907.05388v2: Proposition 5.1 with Eq. (8), proved in Appendix A. <https://arxiv.org/abs/1907.05388v2>
