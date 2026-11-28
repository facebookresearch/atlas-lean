# Finite-step optimal values have span at most the diameter

In an MDP with rewards in $[0,1]$ and diameter $D$, the optimal expected total reward over $i$ steps, as a function of the start state, varies by at most $D$ between any two states, for every $i$.

Let $M$ be a finite MDP with mean rewards $\bar r(s, a) \in [0, 1]$ and finite [diameter](diameter-of-an-mdp.md) $D$. For $i \ge 0$ let $u_i(s)$ be the largest expected total reward of the first $i$ steps over all policies, non-stationary ones included, started in state $s$; equivalently $u_0 \equiv 0$ and $u_{i+1}(s) = \max_a \big(\bar r(s, a) + \sum_{s'} p(s' \mid s, a)\, u_i(s')\big)$. Then for every $i \ge 0$

$$
\max_{s} u_i(s) - \min_{s} u_i(s) \le D.
$$

The same holds for the iterates of [extended value iteration](ucrl2-and-extended-value-iteration.md), $u_0 \equiv 0$ and $u_{i+1}(s) = \max_a \big(\tilde r(s, a) + \max_{q \in \mathcal{P}(s, a)} \sum_{s'} q(s')\, u_i(s')\big)$, where $\tilde r(s, a)$ is the largest plausible reward and $\mathcal{P}(s, a)$ the polytope of plausible transition laws of a UCRL2 confidence set that contains $M$: these are the optimal $i$-step values of the extended MDP whose actions at $(s, a)$ are all pairs of a plausible reward in $[0, 1]$ and a plausible transition law, which include the actions of $M$.

## Depends on

- [Diameter of a Markov decision process](diameter-of-an-mdp.md)
- [Finite-horizon value](../../../not-yet-classified/finite-horizon/finite-horizon-value.md)
- [UCRL2 and extended value iteration](ucrl2-and-extended-value-iteration.md)

## Proof depends on

None.

## Expansion

Suppose $u_i(s'') - u_i(s') > D$. From $s'$, first follow a stationary policy that reaches $s''$ fastest, which takes at most $D$ steps in expectation, and then follow an optimal $i$-step policy for $s''$. At most $D$ of the $i$ rewards of that policy are missed in expectation, each at most $1$, and the rewards collected on the way are nonnegative, so this non-stationary policy earns at least $u_i(s'') - D$ from $s'$, contradicting the optimality of $u_i(s')$.

In the notation of the [finite-horizon value](../../../not-yet-classified/finite-horizon/finite-horizon-value.md), $u_i = V_i$ with discount $1$. The reward bound on the added actions is needed: an added action with reward $100$ in one state of an MDP whose rewards are all $0$ gives $u_1$ span $100$ whatever the diameter. The argument also needs the maxima to be attained, so that an optimal $i$-step policy of the extended MDP exists. For the UCRL2 sets they are: the inner maximum is a linear function over the polytope of plausible laws, an $\ell_1$ ball around the empirical law intersected with the probability simplex, and the reward part is the largest plausible reward, which lies in $[0, 1]$ because plausible rewards are mean rewards of plausible MDPs. Compactness of the action sets suffices for attainment in general; without it attainment can fail, for example with two states, a zero-reward action that switches states (diameter $1$), and added actions of rewards $1 - 1/n$, $n \ge 2$, at one state, where the maximum defining $u_1$ is not attained. Since the extended MDP contains the actions of $M$, its diameter is at most that of $M$ as long as $M$ is plausible, so the iterates have span at most $D(M)$. Centering the iterates, so that they lie in an interval of length at most $D$, lets the analysis bound $(\tilde p - p)\cdot u_i$ by the $\ell_1$ confidence width of the transition estimates times $D/2$; this is where the factor $D$ in the [UCRL2 regret bound](ucrl2-regret-bound.md) comes from. Jaksch, Ortner and Auer also remark that it bounds by $D$ the span of the bias vector of an optimal policy.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Figure 1, step 4, with (3) and (4) (plausible rewards restricted to $[0, 1]$ and plausible transition laws), Section 3.1 (the plausible rewards and transition laws (1) and (2), the extended MDP, and extended value iteration (5) over the polytope of plausible transition laws), Section 4.3.1, inequality (11) and the argument following it; Remark 8. [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
