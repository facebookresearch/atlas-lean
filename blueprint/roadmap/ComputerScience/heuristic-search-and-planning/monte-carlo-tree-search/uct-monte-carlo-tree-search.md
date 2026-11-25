# UCT Monte-Carlo tree search

UCT plans in a finite-horizon MDP with finitely many actions, given as a simulator that returns
independent samples of the next state and reward. The returns of the planning horizon are scaled to
lie in $[0, 1]$ (scaling per-step rewards to $[0,1]$ does not by itself do this). Each episode starts at
the root and, at every tree node visited, selects an untried action if there is one (in a fixed order);
otherwise it selects an action maximizing $\bar X_{a} + 2 C_p \sqrt{\ln t / s_a}$, where $t$ is the number
of visits of the node, $s_a \ge 1$ the number of times $a$ was selected there and $\bar X_a$ the mean
return observed after selecting $a$, with ties broken by a fixed rule. The episode continues to the
horizon, and the observed return from each visited state and depth is used to update the mean and the
count of the selected action there; estimates are kept per state, depth and action. Selecting an untried
action first is a convention for the case $s_a = 0$, where the bonus is undefined. Each simulator call uses fresh randomness independent of the past.

## Depends on

- [Markov decision process](../value-iteration/mdp.md)

## Sources

- L. Kocsis and Cs. Szepesvári, *Bandit based Monte-Carlo planning*, ECML 2006, LNCS 4212, 282–293: rollout-based planning (Figure 1, with an update at every state and depth of the episode), UCB1 and its bias sequence (equations (1)–(2)), and UCT's selection rule with $c_{t,s} = 2 C_p \sqrt{\ln t / s}$ (Sections 2.2–2.3); rewards scaled to $[0,1]$ (Theorem 6). <https://sites.ualberta.ca/~szepesva/papers/ecml06.pdf>
