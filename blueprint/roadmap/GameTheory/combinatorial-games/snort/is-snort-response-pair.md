# Snort response pairs

In Snort on a finite graph $G$, a pair $(u, v)$ of vertices is a
response pair if $u \neq v$, $u$ and $v$ are not adjacent (so the first player colouring $u$ and
the second answering $v$ is legal), and the first player, now to move, loses from the position
in which the first player has coloured $u$ and the second player has coloured $v$.

The outcome is computed with a bound of $|V(G)| - 2$ further moves, the number of uncoloured
vertices, so the bound never cuts the game short.

## Sources

- Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 3 (response pair).
