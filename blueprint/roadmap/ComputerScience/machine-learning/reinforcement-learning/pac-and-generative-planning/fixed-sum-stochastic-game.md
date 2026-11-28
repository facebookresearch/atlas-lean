# Fixed-sum stochastic game

A fixed-sum two-player stochastic game attaches a matrix game to each state; the joint action pays both players with a constant sum and moves to a random next state. Values of the agent's policies are guaranteed values, minimized over the adversary, and the adversarial $\varepsilon$-return mixing time measures how fast they settle.

**Definition.** A fixed-sum two-player stochastic game $M$ on states $\{1, \dots, N\}$ with actions $A = \{a_1, \dots, a_k\}$ for each of the two players (the agent and the adversary) consists of

- for each state $s$, a stage game in strategic form, whose reward matrix gives the payoffs of the agent and of the adversary for every joint action $(a, a')$, the two payoffs having a constant sum;
- a transition function: $P_M(s, t, a, a') \ge 0$ is the probability of moving from $s$ to $t$ when the agent plays $a$ and the adversary $a'$, with $\sum_t P_M(s, t, a, a') = 1$.

Payoffs are normalized to $[0, R_{\max}]$. A history of length $t$ is a sequence of $t$ triples of state, joint action and rewards, followed by the state reached; a policy of either player maps histories to probability distributions over $A$. An MDP is the special case in which the adversary has a single action.

**Values.** For $T \ge 1$, $U_M(s, \pi, \rho, T)$ is the expected undiscounted average of the agent's payoffs over the first $T$ steps when the agent follows $\pi$ and the adversary follows $\rho$ from state $s$. The agent's guaranteed $T$-step value is $U_M(s, \pi, T) = \min_\rho U_M(s, \pi, \rho, T)$, its long-run value is $U_M(s, \pi) = \liminf_{T \to \infty} U_M(s, \pi, T)$, and $U_M(\pi) = \min_s U_M(s, \pi)$.

**Adversarial mixing time.** For $\varepsilon > 0$, a policy $\pi$ belongs to $\Pi_M(\varepsilon, T)$ if for every start state $s$, every adversary policy $\rho$ and every $t \ge T$, $U_M(s, \pi, \rho, t) > U_M(\pi) - \varepsilon$. The $\varepsilon$-return mixing time of $\pi$ is the smallest $T$ with $\pi \in \Pi_M(\varepsilon, T)$. The source writes $\mathrm{Opt}(\Pi_M(\varepsilon, T))$ for the optimal expected $T$-step undiscounted average return among the policies in $\Pi_M(\varepsilon, T)$; the pages that use it say from which start states it is taken.

## Depends on

None.

## Proof depends on

None.

## Expansion

Stochastic games replace the environment's randomness by an adversary when a stochastic model is inappropriate, and the guaranteed values are probabilistic maximin values. The source argues that the minimum over start states in $U_M(\pi)$ is the right target for learning, since an agent can only learn about states it can visit often, and notes that in irreducible games the optimal long-run value does not depend on the start state and is attained by a stationary policy. For an MDP the adversarial mixing time is a one-sided variant of the [$\varepsilon$-return mixing time](epsilon-return-mixing-time.md) of Kearns and Singh: only $T$-step averages falling short of the long-run value count, with a strict inequality, while Kearns and Singh bound the deviation in both directions. For an ergodic stationary policy it is therefore at most the Kearns–Singh $\varepsilon'$-return mixing time for every $\varepsilon' < \varepsilon$, and it can be much smaller when the averages overshoot their limit.

## Sources

- R. I. Brafman and M. Tennenholtz, "R-max – A General Polynomial Time Algorithm for Near-Optimal Reinforcement Learning", *Journal of Machine Learning Research* 3 (2002), 213–231, [www.jmlr.org](https://www.jmlr.org/papers/volume3/brafman02a/brafman02a.pdf): Definition 1 (Section 2.1, p. 216), the histories, policies and values $U_M$ (p. 217), and the adversarial $\varepsilon$-return mixing time, $\Pi(\varepsilon, T)$ and $\mathrm{Opt}(\Pi(\varepsilon, T))$ (Section 2.2, pp. 217–218).
