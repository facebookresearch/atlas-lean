# Evolutionarily stable strategies of the Hawk–Dove game

In the Hawk–Dove game with resource value $V > 0$ and injury cost $C > 0$ (Hawk vs Hawk yields $(V - C)/2$, Hawk vs Dove yields $V$ and $0$, Dove vs Dove yields $V/2$ each), if $V < C$ the unique evolutionarily stable state plays Hawk with probability $V/C$, and if $V \ge C$ the unique evolutionarily stable state is pure Hawk. More generally, a symmetric game with $2 \times 2$ payoff matrix $A$ has an evolutionarily stable state whenever $A_{11} - A_{21} \ne 0$ and $A_{22} - A_{12} \ne 0$.

## Proof sketch

For $V < C$ the mixed strategy with Hawk probability $V/C$ equalizes the payoffs of Hawk and Dove, and the second-order condition holds because, with $F(s \mid t) = s \cdot A t$, $F(t\mid t) - F(s\mid t)$ is a negative multiple of $(t_H - V/C)^2$. For $V \ge C$ Hawk is a strict or weak best response satisfying the second-order condition.

## Depends on

- [Evolutionarily stable state of a matrix game](../../../../Biology/population-dynamics/stability-of-evolutionarily-stable-states/is-ess.md)

## Proof depends on

- [Evolutionarily stable strategies refine symmetric Nash equilibria](evolutionarily-stable-strategies-refine-symmetric-nash-equilibria.md)

## Sources

- Siddharth Suri, "Computational Evolutionary Game Theory", Algorithmic Game Theory, Cambridge University Press, 2007.
