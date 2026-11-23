# Second-player win in Snort

Let $G$ be a finite simple graph. In Snort on $G$, two
players alternately colour a vertex of $G$ that is not yet coloured, each with their own
colour, and a player may not colour a vertex adjacent to a vertex of the opponent's colour; a
player with no legal move loses. The second player wins Snort on $G$ if, starting from the
position in which no vertex is coloured, the player who moves first has no winning strategy.

Every move colours a new vertex, so the game ends after at most $|V(G)|$ moves and has no
draws; hence this says that the second player has a winning strategy.

## Sources

- Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1.
