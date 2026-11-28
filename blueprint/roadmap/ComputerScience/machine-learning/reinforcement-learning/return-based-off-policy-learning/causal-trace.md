# Causal trace

A sequence of nonnegative coefficients $c_s(a_s, h_s)$, $s \ge 1$, each a fixed function of the current action and the history up to the current state, is called a causal trace; it is called admissible for a target $\pi$ and a behaviour $\mu$ when $\mu(b \mid x_s)\, c_s(b, h_s) \le \pi(b \mid x_s)$ for every action $b$.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$ and a finite nonempty set of actions $A$, every action available in every state. For $s \ge 1$ let $H_s$ be the finite set of histories $h_s = (x_0, a_0, \dots, x_{s-1}, a_{s-1}, x_s)$ of length $s$; a history ends with a state and does not contain the action taken there. A causal trace is a sequence $c = (c_s)_{s \ge 1}$ of functions

$$c_s : A \times H_s \to [0, \infty) .$$

The functions are fixed in advance: they may depend on the policies at hand but not on the Q-function an operator is applied to. Along a trajectory, $c_s$ stands for $c_s(a_s, h_s)$, a function of $(x_0, a_0, \dots, x_s, a_s)$, so no coefficient looks ahead. Products are written $\prod_{s=1}^t c_s$ and equal $1$ for $t = 0$. There is no coefficient $c_0$: the initial action of a trajectory is never weighted. The trace is Markovian when $c_s(b, h_s) = c(b, x_s)$ for one function $c : A \times X \to [0,\infty)$, the same for every $s$, where $x_s$ is the last state of $h_s$.

For stochastic policies $\pi$ (target) and $\mu$ (behaviour), the trace is admissible for $(\pi, \mu)$ when

$$\mu(b \mid x_s)\, c_s(b, h_s) \le \pi(b \mid x_s) \quad \text{for every } s \ge 1, \text{ every } h_s \in H_s \text{ with last state } x_s, \text{ and every } b \in A .$$

Where $\mu(b \mid x_s) > 0$ this is the source's condition $0 \le c_s \le \pi(b \mid x_s)/\mu(b \mid x_s)$; where $\mu(b \mid x_s) = 0$ it imposes nothing, and the value $c_s(b, h_s)$ there never enters an expectation under the behaviour policy, which draws such an action at a time $s \ge 1$ with probability zero.

## Depends on

- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

None.

## Expansion

A definition. Writing admissibility as $\mu c \le \pi$ avoids dividing by $\mu(b \mid x_s)$, which the source's notation $\pi/\mu$ leaves undefined at zero behaviour probabilities; the proofs use only $\pi(b \mid x_s) - \mu(b \mid x_s)\, c_s(b, h_s) \ge 0$. The source writes the history as $\mathcal{F}_s$ and once describes it as the sequence up to time $s$; its proofs condition on $\mathcal{F}_s$ and then average over $a_s \sim \mu(\cdot \mid x_s)$, which requires the history to stop at $x_s$, the reading used here.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 1 (the history $\mathcal{F}_t$), Section 2 (traces $(c_s)$, empty product equal to $1$), Section 3.1 (history-dependent $c_s = c_s(a_s, \mathcal{F}_s)$ and the condition of Theorem 1), Section 3.2 (Markovian traces $c(a_s, x_s)$).
