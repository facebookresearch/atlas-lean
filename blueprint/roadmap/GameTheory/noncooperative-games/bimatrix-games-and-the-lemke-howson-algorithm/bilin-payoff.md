# Expected payoffs in a bimatrix game

Let $M$ and $N$ be finite sets of pure strategies of players 1 and 2, and let $\Delta(M)$ and $\Delta(N)$ be their sets of mixed strategies (probability vectors).
For a payoff matrix $C \in \mathbb{R}^{M \times N}$ and mixed strategies $x \in \Delta(M)$, $y \in \Delta(N)$,
the expected payoff when player 1 plays $x$ and player 2 independently plays $y$ is

$$x^{\mathsf T} C y = \sum_{i \in M} \sum_{j \in N} x_i\, C_{ij}\, y_j$$

(von Stengel, *Algorithmic Game Theory*, Section 3.2).
