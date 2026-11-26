# Evolutionarily stable strategy

Let $A$ be the payoff matrix of a symmetric two-player game on a finite strategy set, and write $F(s \mid t) = s^\top A t$ for the expected fitness of mixed strategy $s$ against $t$. A mixed strategy $s$ is *evolutionarily stable* if for every mixed strategy $t \ne s$ there is $\varepsilon_t > 0$ such that for all $\varepsilon \in (0, \varepsilon_t)$,

$$
(1 - \varepsilon) F(s \mid s) + \varepsilon F(s \mid t) > (1 - \varepsilon) F(t \mid s) + \varepsilon F(t \mid t).
$$

## Depends on

- [Player-symmetric game and symmetric equilibrium](../approximate-and-symmetric-equilibria/player-symmetric-game-and-symmetric-equilibrium.md)
- [Nash equilibrium of a bimatrix game](../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Sources

- Siddharth Suri, "Computational Evolutionary Game Theory", Algorithmic Game Theory, Cambridge University Press, 2007.
