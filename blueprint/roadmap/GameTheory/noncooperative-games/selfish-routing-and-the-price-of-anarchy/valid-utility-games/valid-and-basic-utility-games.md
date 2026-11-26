# Valid and basic utility games

A *utility game* has players $i$ choosing strategies from finite sets $S_i$ of elements of a ground set, a social value function $V$ on finite sets of chosen elements, and utilities $u_i(s)$. Writing $V(s)$ for $V$ of the chosen set and $s - s_i$ for the profile with $i$'s element removed, the game is *valid* if $V$ is submodular, $\sum_i u_i(s) \le V(s)$, and $u_i(s) \ge V(s) - V(s - s_i)$ for all $i$ and $s$; it is *basic* if moreover $u_i(s) = V(s) - V(s - s_i)$ exactly. It is *monotone* if $V$ is monotone.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Adrian Vetta, "Nash Equilibria in Competitive Societies, with Applications to Facility Location, Traffic Routing and Auctions", 43rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2002), 2002.
