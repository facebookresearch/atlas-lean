# R-max algorithm

R-max keeps a complete but optimistic model: every joint action not yet tried often enough is assumed to pay the maximal reward and to lead to a fictitious absorbing state. It always follows an optimal $T$-step policy of this model, so it explores or exploits without deciding which.

Let $M$ be a [fixed-sum stochastic game](fixed-sum-stochastic-game.md) on $N$ states with $k$ actions per player and payoffs in $[0, R_{\max}]$, with $R_{\max} > 0$, and let $U_M$, $\Pi_M(\varepsilon, T)$ and $\mathrm{Opt}$ be as defined there.

The agent observes the current state, the adversary's action and the payoffs after each stage, and knows $R_{\max}$.

**Algorithm (R-max).** Inputs: $N$, $k$, the error bound $\varepsilon > 0$, the failure probability $\delta \in (0, 1)$, $R_{\max}$, the $\varepsilon$-return mixing time $T \ge 1$ of an optimal policy, and a visit threshold $K_1 \ge 1$.

1. *Initialize.* Build a model $M'$ with stage games $G_0, G_1, \dots, G_N$, where $G_0$ is fictitious; every entry of every game matrix is $(R_{\max}, 0)$ and $P_{M'}(G_i, G_0, a, a') = 1$ for $i = 0, \dots, N$ and all joint actions. Each entry of $G_1, \dots, G_N$ carries a flag, initially unknown, the multiset of states reached by playing it and its observed reward.
2. *Repeat.*
   - *Compute and act:* compute an optimal $T$-step policy of the current model for the current state $s$, that is, an agent policy maximizing the guaranteed value $\min_\rho U_{M'}(s, \pi, \rho, T)$, and execute it for $T$ steps or until a new entry becomes known.
   - *Observe and update:* after each joint action $(a, a')$ in $G_i$, record the observed reward on the first play of the entry and the state reached; once the record of states reached from the entry has $K_1$ elements, mark the entry known and set its transition probabilities to the observed frequencies.

The source requires that $K_1$ samples of an entry estimate each of its transition probabilities within $\varepsilon/(2N T R_{\max})$, with failure probability small enough for a union bound, and prints the choice

$$K_1 = \max\Big(\Big\lceil \Big(\frac{4 N T R_{\max}}{\varepsilon}\Big)^3 \Big\rceil, \Big\lceil -6\ln^3\Big(\frac{\delta}{6 N k^2}\Big)\Big\rceil\Big) + 1.$$

Its union bound runs over $N k^2$ events, whereas the model has $N^2 k^2$ transition probabilities ($N$ successor states for each of the $N k^2$ entries), so the guarantee is stated for any polynomially bounded threshold that meets the requirement rather than for this closed form.

**Induced game.** For a set $L$ of entries marked unknown, the induced game $M_L$ equals $M$ with an extra state $G_0$, except that every entry in $L$ and every entry of $G_0$ moves to $G_0$ with probability $1$ and pays $R_{\max}$ to the agent and $0$ to the adversary. The R-max policy for $M_L$ from a state $s$ is an optimal $T$-step policy of $M_L$ from $s$ in the maximin sense above.

## Depends on

- [Fixed-sum stochastic game](fixed-sum-stochastic-game.md)

## Proof depends on

None.

## Expansion

*How it behaves.* The optimistic payoff of the fictitious state makes unvisited entries attractive, so an optimal policy of the model either earns near-optimal reward on the known part of the game or reaches an unknown entry with noticeable probability; this is the implicit explore or exploit property. The model has $N k^2$ entries, each learned after $K_1$ visits, which bounds the number of exploration phases. An unknown $T$ is handled by running the algorithm with $T = 1, 2, \dots$ in turn; the computation then eventually becomes exponential in the true mixing time, as it does for E3. Analyses of discounted MDPs use the same algorithm with a fixed visit threshold $m$, an admissible optimistic initial value instead of $R_{\max}$, and empirical rewards.

*What an expansion contains.* The step "compute an optimal $T$-step policy" presupposes that a finite-horizon fixed-sum stochastic game has a $T$-step maximin value from each state and an agent policy attaining it. A sound expansion adds:

1. a page stating that for a fixed-sum stochastic game with finitely many states and actions and every $T \ge 1$, backward induction over the $T$ stages, solving at each stage and state the matrix game of stage payoffs plus continuation values, yields an agent policy (history-dependent through the time step, mixed at each stage) maximizing $\min_\rho U_M(s, \pi, \rho, T)$ from every state $s$; its stage step is [von Neumann's minimax theorem](../../../algebraic-and-numerical-algorithms/linear-programs-as-symmetric-zero-sum-games/minimax-theorem-over-ordered-fields.md);
2. a page for the induced game $M_L$ of a set $L$ of unknown entries, defined above, so that the algorithm and the [Implicit Explore or Exploit Lemma](implicit-explore-or-exploit-lemma.md) share it.

With these pages listed under the dependency sections, the algorithm page no longer needs to be held.

## Sources

- R. I. Brafman and M. Tennenholtz, "R-max – A General Polynomial Time Algorithm for Near-Optimal Reinforcement Learning", *Journal of Machine Learning Research* 3 (2002), 213–231, [www.jmlr.org](https://www.jmlr.org/papers/volume3/brafman02a/brafman02a.pdf): Section 2.2 (the agent's observations and knowledge of $R_{\max}$, p. 217), Section 3 (algorithm, p. 219), Definition 5 (induced game, p. 222) and the discussion of unknown mixing times (p. 227).
