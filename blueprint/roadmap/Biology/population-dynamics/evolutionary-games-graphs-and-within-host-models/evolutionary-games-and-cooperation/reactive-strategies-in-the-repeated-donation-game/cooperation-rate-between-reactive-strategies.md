# Cooperation rate between reactive strategies

In the repeated donation game, a cooperator pays $c > 0$ to give the co-player $b > c$; a defector pays and gives nothing. A *reactive strategy* is a pair $(p, q) \in [0,1]^2$: cooperate with probability $p$ if the co-player cooperated in the previous round and with probability $q$ if the co-player defected. Examples: ALLD $= (0,0)$, ALLC $= (1,1)$, Tit-for-Tat $= (1,0)$, generous Tit-for-Tat $= (1, q)$.

Let player 1 use $(p_1, q_1)$ and player 2 use $(p_2, q_2)$, moving simultaneously each round, and put $\varrho_i = p_i - q_i$. If $|\varrho_1\varrho_2| < 1$, the probabilities $c_1, c_2$ that each player cooperates converge, from any first move, to

$$c_1 = \frac{q_1 + \varrho_1 q_2}{1 - \varrho_1\varrho_2}, \qquad c_2 = \frac{q_2 + \varrho_2 q_1}{1 - \varrho_1\varrho_2},$$

and player 1's long-run payoff per round is $\pi\big((p_1,q_1),(p_2,q_2)\big) = b\,c_2 - c\,c_1$. The cooperation rate of a strategy against itself is $C(s,s) = q/(1 - \varrho)$.

## Proof sketch

Player 1 cooperates in round $t+1$ with probability $q_1 + \varrho_1 x_2(t)$, where $x_2(t)$ is the probability that player 2 cooperated in round $t$, and symmetrically. The pair $(x_1, x_2)$ thus follows the affine map $x_1 \mapsto q_1 + \varrho_1 x_2$, $x_2 \mapsto q_2 + \varrho_2 x_1$, whose two-step map contracts by $\varrho_1\varrho_2$; when $|\varrho_1\varrho_2| < 1$ it converges to the unique fixed point, obtained by solving $c_1 = q_1 + \varrho_1(q_2 + \varrho_2 c_1)$. Payoffs are linear in the cooperation rates because each round's payoff is $b$ times the co-player's cooperation minus $c$ times one's own. The case $|\varrho_1\varrho_2| = 1$ arises only for pairs of deterministic strategies such as Tit-for-Tat against itself, where the outcome depends on the first move.

## Sources

- J. Tkadlec, C. Hilbe, M. A. Nowak, "Mutation enhances cooperation in direct reciprocity", Proceedings of the National Academy of Sciences of the USA (2023), <https://doi.org/10.1073/pnas.2221080120> (PMC10193978).
- M. A. Nowak, K. Sigmund, "The evolution of stochastic strategies in the Prisoner's Dilemma", Acta Applicandae Mathematicae 20 (1990) 247–265, <https://doi.org/10.1007/BF00049570>.
