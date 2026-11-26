# Evolutionarily stable strategies refine symmetric Nash equilibria

Let $A$ be the payoff matrix of a symmetric two-player game on a finite strategy set, and write $F(s \mid t) = s \cdot A t$ for the expected fitness of mixed strategy $s$ against $t$. A mixed strategy $s$ satisfies, for every mixed strategy $t \ne s$ and every $\varepsilon \in (0, \varepsilon_t)$ for some $\varepsilon_t > 0$, the invasion inequality

$$
(1 - \varepsilon) F(s \mid s) + \varepsilon F(s \mid t) > (1 - \varepsilon) F(t \mid s) + \varepsilon F(t \mid t),
$$

if and only if $s$ is an evolutionarily stable state of $A$. In particular, then $(s, s)$ is a symmetric Nash equilibrium, and every best response $t \ne s$ to $s$ satisfies $F(t \mid t) < F(s \mid t)$.

## Proof sketch

The invasion inequality reads $(1 - \varepsilon)\bigl(F(s \mid s) - F(t \mid s)\bigr) + \varepsilon\bigl(F(s \mid t) - F(t \mid t)\bigr) > 0$. It holds for all small enough $\varepsilon > 0$ exactly when $F(t \mid s) < F(s \mid s)$, or $F(t \mid s) = F(s \mid s)$ and $F(t \mid t) < F(s \mid t)$, which are the two conditions defining an evolutionarily stable state.

## Depends on

- [Evolutionarily stable state of a matrix game](../../../../Biology/population-dynamics/stability-of-evolutionarily-stable-states/is-ess.md)
- [Player-symmetric game and symmetric equilibrium](../../nash-s-theorem/approximate-and-symmetric-equilibria/player-symmetric-game-and-symmetric-equilibrium.md)

## Sources

- Siddharth Suri, "Computational Evolutionary Game Theory", Algorithmic Game Theory, Cambridge University Press, 2007.
