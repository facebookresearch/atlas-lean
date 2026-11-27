# Networked coordination game and contagion threshold

On a locally finite simple graph $G$, each vertex chooses behaviour $A$ or $B$ and plays a symmetric coordination game with each neighbour; in the normalized game with parameter $q$, matching on $A$ pays $q$, matching on $B$ pays $1 - q$ and mismatching pays $0$. With adopters $S$ fixed, $B$ is a best response at $v$ iff $q\, \deg(v) \le |N(v) \cap S|$. The best-response step is $h_q(S) = \{v : q \deg(v) \le |N(v) \cap S|\}$ and the progressive step is $\bar h_q(S) = S \cup h_q(S)$. A finite set $S$ is *contagious* if under iteration every vertex eventually adopts $B$ permanently. The *contagion threshold* of $G$ is the supremum of $q \in [0, 1]$ for which some finite set is contagious.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Pure Nash equilibrium of a finite game](../is-pure-nash-2.md)

## Sources

- Jon Kleinberg, "Cascading Behavior in Networks: Algorithmic and Economic Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
- Stephen Morris, "Contagion", Review of Economic Studies, 2000.
