# Strictly dominated actions are not played in a pure Nash equilibrium

In a normal-form game with nonempty action sets, suppose action $a_i$ of player $i$ is strictly dominated by an action $b_i$: $u_i(b_i, a_{-i}) > u_i(a_i, a_{-i})$ for every profile $a_{-i}$ of the others. Then no pure Nash equilibrium has player $i$ playing $a_i$. In a finite game, if $a_i$ is strictly dominated by a mixed strategy $\sigma_i$ ($\sum_b \sigma_i(b)u_i(b, a_{-i}) > u_i(a_i, a_{-i})$ for every $a_{-i}$), then $a_i$ has probability zero in every mixed Nash equilibrium. Weakly dominated actions can be played in equilibrium: in the game where both players get $1$ at $(T, L)$ and $0$ elsewhere, $(B, R)$ is a Nash equilibrium although $B$ and $R$ are weakly dominated.

## Proof depends on

- [Pure Nash equilibrium](../potential-games/is-pure-nash.md): the pure equilibrium condition, with costs $-u_i$.
- [Mixed Nash equilibrium](is-mixed-nash.md): the mixed equilibrium condition.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
