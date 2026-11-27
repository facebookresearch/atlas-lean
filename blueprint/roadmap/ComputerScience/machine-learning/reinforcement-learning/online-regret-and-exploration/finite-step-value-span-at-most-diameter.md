# Finite-step optimal values have span at most the diameter

In an MDP with rewards in $[0,1]$ and diameter $D$, the optimal expected total reward over $i$ steps, as a function of the start state, varies by at most $D$ between any two states, for every $i$.

Let $M$ be a finite MDP with mean rewards $\bar r(s, a) \in [0, 1]$ and finite [diameter](diameter-of-an-mdp.md) $D$. For $i \ge 0$ let $u_i(s)$ be the largest expected total reward of the first $i$ steps over all policies, non-stationary ones included, started in state $s$; equivalently $u_0 \equiv 0$ and $u_{i+1}(s) = \max_a \big(\bar r(s, a) + \sum_{s'} p(s' \mid s, a)\, u_i(s')\big)$. Then for every $i \ge 0$

$$
\max_{s} u_i(s) - \min_{s} u_i(s) \le D.
$$

The same holds when the maximum in the recursion also ranges over any set of alternative actions, each with a mean reward in $[0, 1]$ and a transition law on $\mathcal{S}$, as long as the actions of $M$ are among them.

## Depends on

- [Diameter of a Markov decision process](diameter-of-an-mdp.md)

## Proof depends on

None.

## Expansion

Suppose $u_i(s'') - u_i(s') > D$. From $s'$, first follow a stationary policy that reaches $s''$ fastest, which takes at most $D$ steps in expectation, and then follow an optimal $i$-step policy for $s''$. At most $D$ of the $i$ rewards of that policy are missed in expectation, each at most $1$, and the rewards collected on the way are nonnegative, so this non-stationary policy earns at least $u_i(s'') - D$ from $s'$, contradicting the optimality of $u_i(s')$.

The reward bound on the added actions is needed: an added action with reward $100$ in one state of an MDP whose rewards are all $0$ gives $u_1$ span $100$ whatever the diameter. In UCRL2 this is applied to the iterates of extended value iteration on the optimistic MDP whose action set contains every plausible transition law, with plausible rewards in $[0, 1]$: its diameter is at most that of the true MDP $M$ as long as $M$ is plausible, so the iterates have span at most $D(M)$. Centering the iterates, so that they lie in an interval of length at most $D$, lets the analysis bound $(\tilde p - p)\cdot u_i$ by the $\ell_1$ confidence width of the transition estimates times $D/2$; this is where the factor $D$ in the [UCRL2 regret bound](ucrl2-regret-bound.md) comes from. Jaksch, Ortner and Auer also remark that it bounds by $D$ the span of the bias vector of an optimal policy.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Section 4.3.1, inequality (11) and the argument following it; Remark 8. [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
