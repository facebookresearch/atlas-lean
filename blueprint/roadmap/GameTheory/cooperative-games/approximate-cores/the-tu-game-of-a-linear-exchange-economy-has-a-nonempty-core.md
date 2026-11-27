# The TU game of a linear exchange economy has a nonempty core

Let finitely many agents hold nonnegative endowments $e_{ig}$ of finitely many divisible goods and have linear utilities $u_i(x) = \sum_g a_{ig} x_g$ with $a_{ig} \ge 0$. Define the transferable-utility game whose value $v(S)$ is the maximum total utility coalition $S$ can obtain by redistributing its own endowments. Then $v(S)$ is attained by a feasible redistribution, $v(S) = \sum_g \bigl(\max_{i \in S} a_{ig}\bigr) \sum_{i \in S} e_{ig}$ for nonempty $S$, and the payoff vector that pays each agent the value of its endowment at the prices $p_g = \max_k a_{kg}$, namely $x_i = \sum_g p_g\, e_{ig}$, lies in the core of this game; in particular the core is nonempty.

## Proof sketch

With linear utilities, the optimum for a coalition gives each good to a member valuing it most. Pricing each good at the maximum marginal utility in the grand coalition and paying each agent the value of its endowment gives a payoff vector that no coalition can improve on, since each coalition's value is at most the price of its endowment.

## Depends on

- [Cooperative game with transferable utility](../shapley-value/coop-game.md)
- [Core allocation](../bondareva-shapley-theorem/is-core-allocation.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007, Exercise 15.1.
