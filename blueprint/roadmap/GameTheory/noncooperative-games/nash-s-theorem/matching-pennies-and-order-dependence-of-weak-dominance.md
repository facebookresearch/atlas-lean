# Matching pennies has no pure equilibrium; weak-dominance elimination depends on order

(Matching pennies.) In the game with payoffs $(1, -1)$ when the two players' choices match and $(-1, 1)$ when they differ, every pure profile gives one player a profitable deviation, so there is no pure Nash equilibrium; the unique Nash equilibrium has each player mix with probability $1/2$.

(Order dependence of weak dominance.) Let player 1 choose $T, M, B$ and player 2 choose $L, R$, with payoffs $(1,1), (0,0)$ in row $T$, $(1,1), (2,1)$ in row $M$ and $(0,0), (2,1)$ in row $B$. Both $T$ and $B$ are weakly dominated by $M$. Removing $T$ first makes $L$ weakly dominated by $R$, leaving $\{M, B\} \times \{R\}$; removing $B$ first makes $R$ weakly dominated by $L$, leaving $\{T, M\} \times \{L\}$. The two orders leave different sets of profiles with different payoffs.

## Proof depends on

- [Pure Nash equilibrium of a finite game](../potential-games/is-pure-nash-2.md): the pure equilibrium condition.
