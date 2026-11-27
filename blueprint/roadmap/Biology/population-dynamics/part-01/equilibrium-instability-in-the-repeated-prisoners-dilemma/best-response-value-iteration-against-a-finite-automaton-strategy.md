# Best response value iteration against a finite-automaton strategy

**Setting.** In the repeated prisoner's dilemma with continuation probability $\delta \in [0,1)$, let $S$ be a strategy implemented by a finite automaton with states $\{1, \dots, N_S\}$ and initial state $1$: in state $i$ it plays $\lambda_S(i) \in \{C, D\}$ and moves to state $\mu_S(i, a)$ when its opponent plays $a$. Let $\pi_1(a, b)$ be the stage payoff to a player choosing $a$ against $b$. The values $V_S^*(i)$ to an opponent of $S$ being in state $i$ solve the Bellman system

$$V_S(i) = \max_{a \in \{C, D\}} \bigl\{\pi_1(a, \lambda_S(i)) + \delta\, V_S(\mu_S(i, a))\bigr\}, \qquad i = 1, \dots, N_S.$$

**Lemma.** Start from any $V_{S,1}$ with $V_{S,1}(i) \le V_S^*(i)$ for all $i$ (for example $V_{S,1} \equiv 0$ when payoffs are non-negative) and iterate

$$V_{S,n+1}(i) = \max_{a} \bigl\{\pi_1(a, \lambda_S(i)) + \delta\, V_{S,n}(\mu_S(i, a))\bigr\}.$$

Then $0 \le \max_i \bigl(V_S^*(i) - V_{S,n+1}(i)\bigr) \le \delta \max_i \bigl(V_S^*(i) - V_{S,n}(i)\bigr)$, so $V_{S,n} \to V_S^*$ geometrically. The maximal discounted payoff against $S$ is $(1-\delta)V_S^*(1)$, attained by playing $a_i^* = \arg\max_a\{\pi_1(a, \lambda_S(i)) + \delta V_S^*(\mu_S(i, a))\}$ whenever $S$ is in state $i$. Hence $S$ is a Nash equilibrium if and only if its payoff against itself equals $(1-\delta)V_S^*(1)$.

## Depends on

- [Indirect invasions destabilize every equilibrium of the repeated prisoner's dilemma](indirect-invasions-destabilize-every-equilibrium-of-the-repeated-prisoners-dilemma.md)
- [Bellman optimality operator](../../../../ComputerScience/heuristic-search-and-planning/value-iteration/bellman.md)
- [The Bellman optimality operator is monotone](../../../../ComputerScience/heuristic-search-and-planning/value-iteration/bellman-mono.md)
- [Bellman's operator is a contraction](../../../../ComputerScience/heuristic-search-and-planning/value-iteration/bellman-contracting.md)
- [Value iteration converges](../../../../ComputerScience/heuristic-search-and-planning/value-iteration/tendsto-value-iteration.md)

## Expansion

Facing a fixed automaton, the opponent solves a finite discounted Markov decision problem whose state is the automaton's state. Monotonicity of the Bellman operator keeps the iterates below $V_S^*$; plugging the optimal action $a_i^*$ into the iteration shows the gap contracts by $\delta$. This turns the infinite comparison against all strategies into a finite computation, which lets simulations check whether populations visit Nash equilibria.

## Sources

- J. García and M. van Veelen, "No Strategy Can Win in the Repeated Prisoner's Dilemma: Linking Game Theory and Computer Simulations", *Frontiers in Robotics and AI* 5 (2018) 102, Section 5.2 ("Verifying Nash equilibria"), the best responder iteration and Lemma 1. <https://doi.org/10.3389/frobt.2018.00102> (PMC7805755)
