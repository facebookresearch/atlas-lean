# Size of the graphical representation

If $|S_i| \le k$ for all players and every vertex of $G$ has degree at most $d$, the local tables of a graphical game on $n$ players contain at most $n k^{d+1}$ entries, whereas with $|S_i| = k$ for all players the normal form contains $n k^n$ entries; the graphical representation is strictly smaller whenever $G$ is not complete and every player has at least two strategies. A normal-form game is representable as a graphical game on $G$ if and only if each player's payoff depends only on the actions in its closed neighbourhood.

## Proof sketch

Count the table entries per player; dependence only on $N[i]$ is exactly the condition for the payoff to factor through the restriction.

## Depends on

- [Graphical game](graphical-game.md)
- [Explicit encoding and size of finite games](../../explicit-encoding-and-size-of-finite-games.md)

## Sources

- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007.
