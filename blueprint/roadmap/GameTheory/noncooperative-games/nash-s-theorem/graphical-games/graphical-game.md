# Graphical game

A *graphical game* on players $I$ with strategy sets $S_i$ is given by an undirected graph $G$ on $I$ and, for each player $i$, a local payoff table $u_i : \prod_{j \in N[i]} S_j \to \mathbb{R}$ on the closed neighbourhood $N[i] = \{i\} \cup N(i)$. Player $i$'s payoff at a global profile $s$ is $u_i(s|_{N[i]})$. Every normal-form game is a graphical game on the complete graph.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)

## Sources

- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007.
