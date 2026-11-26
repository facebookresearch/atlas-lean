# Evolutionarily stable strategies refine symmetric Nash equilibria

In a finite symmetric two-player game with fitness $F$, a mixed strategy $s$ is evolutionarily stable if and only if $(s, s)$ is a Nash equilibrium and every best response $t \ne s$ to $s$ satisfies $F(t \mid t) < F(s \mid t)$.

## Proof sketch

Letting $\varepsilon \to 0$ in the invasion inequality gives $F(s\mid s) \ge F(t \mid s)$, with equality forcing the second-order condition. Conversely the two conditions make the invasion inequality hold for small $\varepsilon$ depending on $t$.

## Depends on

- [Evolutionarily stable strategy](evolutionarily-stable-strategy.md)
- [Player-symmetric game and symmetric equilibrium](../../nash-s-theorem/approximate-and-symmetric-equilibria/player-symmetric-game-and-symmetric-equilibrium.md)

## Sources

- Siddharth Suri, "Computational Evolutionary Game Theory", Algorithmic Game Theory, Cambridge University Press, 2007.
