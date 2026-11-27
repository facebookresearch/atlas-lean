# R-max algorithm

R-max keeps a complete but optimistic model: every joint action not yet tried often enough is assumed to pay the maximal reward and to lead to a fictitious absorbing state. It always follows an optimal $T$-step policy of this model, so it explores or exploits without deciding which.

**Fixed-sum stochastic games.** A fixed-sum two-player stochastic game $M$ on states $\{1, \dots, N\}$ (stage games $G_1, \dots, G_N$) with actions $A = \{a_1, \dots, a_k\}$ for both players assigns to each state a stage game in strategic form, whose reward matrix gives the payoffs of the agent and of the adversary for each joint action $(a, a')$, with a constant payoff sum, and a transition function $P_M(s, t, a, a')$, the probability of moving from $s$ to $t$ when the agent plays $a$ and the adversary $a'$. Payoffs are normalized to $[0, R_{\max}]$. An MDP is the special case in which the adversary has a single action. Policies map histories (sequences of states, joint actions and rewards) to distributions over actions. $U_M(s, \pi, \rho, T)$ denotes the expected $T$-step undiscounted average reward of agent policy $\pi$ against adversary policy $\rho$ from $s$, $U_M(s, \pi, T) = \min_\rho U_M(s, \pi, \rho, T)$, $U_M(s, \pi) = \liminf_{T\to\infty} U_M(s, \pi, T)$ and $U_M(\pi) = \min_s U_M(s, \pi)$.

**Adversarial mixing time.** A policy $\pi$ belongs to $\Pi(\varepsilon, T)$ if for every start state $s$, every adversary behaviour $\rho$ and every $t \ge T$, $U(s, \pi, \rho, t) > U(\pi) - \varepsilon$; the $\varepsilon$-return mixing time of $\pi$ is the smallest such $T$, and the source writes $\mathrm{Opt}(\Pi(\varepsilon, T))$ for the optimal expected $T$-step undiscounted average return among policies in $\Pi(\varepsilon, T)$. Expected $T$-step returns are guaranteed values, minimized over adversary policies; the lemma and theorem pages fix the start state explicitly.

The agent observes the current state, the adversary's action and the payoffs after each stage, and knows $R_{\max}$.

**Algorithm (R-max).** Inputs: $N$, $k$, the error bound $\varepsilon$, the failure probability $\delta$, $R_{\max}$ and the $\varepsilon$-return mixing time $T$ of an optimal policy.

1. *Initialize.* Build a model $M'$ with stage games $G_0, G_1, \dots, G_N$, where $G_0$ is fictitious; every entry of every game matrix is $(R_{\max}, 0)$ and $P_{M'}(G_i, G_0, a, a') = 1$ for $i = 0, \dots, N$ and all joint actions. Each entry of $G_1, \dots, G_N$ carries a flag, initially unknown, the multiset of states reached by playing it and its observed reward.
2. *Repeat.*
   - *Compute and act:* compute an optimal $T$-step policy of the current model for the current state $s$, that is, an agent policy maximizing the guaranteed value $\min_\rho U_{M'}(s, \pi, \rho, T)$, and execute it for $T$ steps or until a new entry becomes known.
   - *Observe and update:* after each joint action $(a, a')$ in $G_i$, record the observed reward on the first play of the entry and the state reached; once the record of states reached from the entry has $K_1$ elements, mark the entry known and set its transition probabilities to the observed frequencies.

The visit threshold $K_1$ is a parameter. The source requires that $K_1$ samples of an entry estimate each of its transition probabilities within $\varepsilon/(2N T R_{\max})$, with failure probability small enough for a union bound, and prints the choice

$$K_1 = \max\Big(\Big\lceil \Big(\frac{4 N T R_{\max}}{\varepsilon}\Big)^3 \Big\rceil, \Big\lceil -6\ln^3\Big(\frac{\delta}{6 N k^2}\Big)\Big\rceil\Big) + 1.$$

Its union bound runs over $N k^2$ events, whereas the model has $N^2 k^2$ transition probabilities ($N$ successor states for each of the $N k^2$ entries), so the guarantee is stated for a threshold that meets the requirement rather than for this closed form.

**Induced game.** For a set $L$ of entries marked unknown, the induced game $M_L$ equals $M$ with an extra state $G_0$, except that every entry in $L$ and every entry of $G_0$ moves to $G_0$ with probability $1$ and pays $R_{\max}$ to the agent and $0$ to the adversary. The R-max policy for $M_L$ from a state $s$ is an optimal $T$-step policy of $M_L$ from $s$ in the maximin sense above.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

The optimistic payoff of the fictitious state makes unvisited entries attractive, so an optimal policy of the model either earns near-optimal reward on the known part of the game or reaches an unknown entry with noticeable probability; this is the implicit explore or exploit property. The model has $N k^2$ entries, each learned after $K_1$ visits, which bounds the number of exploration phases. An unknown $T$ is handled by running the algorithm with $T = 1, 2, \dots$ in turn; the computation then eventually becomes exponential in the true mixing time, as it does for E3. Analyses of discounted MDPs use the same algorithm with a fixed visit threshold $m$, an admissible optimistic initial value instead of $R_{\max}$, and empirical rewards.

## Sources

- R. I. Brafman and M. Tennenholtz, "R-max – A General Polynomial Time Algorithm for Near-Optimal Reinforcement Learning", *Journal of Machine Learning Research* 3 (2002), 213–231, [www.jmlr.org](https://www.jmlr.org/papers/volume3/brafman02a/brafman02a.pdf): Definition 1 and Sections 2.1–2.2 (pp. 215–218), Section 3 (algorithm, p. 219), Definition 5 (induced game, p. 222) and the discussion of unknown mixing times (p. 227).
