# Snort positions with a move bound

Let $G$ be a finite simple graph, let $k$ be a natural
number, and let $A$ and $B$ be finite sets of vertices of $G$, the vertices coloured so far by
the player to move and by the opponent. A legal move colours a vertex $v$ that lies in neither
$A$ nor $B$ and has no neighbour in $B$. With move bound $0$ the player to move loses. With move
bound $k + 1$ the player to move wins at $(A, B)$ exactly when some legal move $v$ leaves a
position $(B, A \cup \{v\})$ that the opponent, now to move with move bound $k$, does not win.

## Sources

- Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1 (rules of Snort).
